import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell093.Parameters
import ForestUnimodality.BinomialMassData.Q107_207.Batch000_049
import ForestUnimodality.BinomialMassData.Q107_207.Batch050_099
import ForestUnimodality.BinomialMassData.Q107_207.Batch100_149
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch000_049
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch050_099
import ForestUnimodality.BinomialMassData.Q7427_14352.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree000.table
  base := (76154706920999334836253069/1250000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (794090746533374497451163170000000000000)
      linear := (-31646114527807403180026391000000000000)
      constant := (609237655367994678690024552000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree000.table
  base := (76154706920999334836253069/1250000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (794090746533374497451163170000000000000)
      linear := (-31646114527807403180026391000000000000)
      constant := (609237655367994678690024552000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree001.table
  base := (336349924551196902575944730860209203579771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-36532636251337442906952576932619000000000000)
      constant := (14422050391841973089271008544296693164189607579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree001.table
  base := (336044398580219704707373882486289192431499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-686743703705295216382165430766147750000000000)
      constant := (270568626946821072204945516282501980340928478891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9993880929153331779/20000000000000000000)
  directionHi := (3123087790360416181/6250000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree002.table
  base := (1565958075732194594576756735916541560091/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-71709268141272866395044203037279000000000000)
      constant := (8425235237790696003708773449762824163542407375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree002.table
  base := (7817240071312561616398112800696129243743/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-1348024658846485845899053007096176500000000000)
      constant := (157956307334791971901871475308080145773220287175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9993880929153331779/20000000000000000000)
  centralHi := (3123087790360416181/6250000000000000000)
  directionLo := (35333704876876176181/50000000000000000000)
  directionHi := (70667409753752352363/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree003.table
  base := (121537350967768118199223662540968811138779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-11876211114578698875903981015771000000000000)
      constant := (587964516178163417425500359335635509831726819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree003.table
  base := (6064519118671979027225030630722009888741/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-223256179331964052823993398158467250000000000)
      constant := (11018976465146096554128773494212244754079182820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35333704876876176181/50000000000000000000)
  centralHi := (70667409753752352363/100000000000000000000)
  directionLo := (21637386917609037587/25000000000000000000)
  directionHi := (86549547670436150349/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree004.table
  base := (40462904890967153209751595607962217231607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-142062531921143713371227455246599000000000000)
      constant := (3615858461821778394402523732681462092314256686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree004.table
  base := (10093409468692062012661289040636131289047/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-2670586569128867104932828159756234000000000000)
      constant := (67760335724788702001120584837031116057790540984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21637386917609037587/25000000000000000000)
  centralHi := (86549547670436150349/100000000000000000000)
  directionLo := (99938809291533317791/100000000000000000000)
  directionHi := (3123087790360416181/3125000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree005.table
  base := (57535310516312837543667782410305067743431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-177239163811079136859319081351259000000000000)
      constant := (2696123793193385922306752009503706847738274919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree005.table
  base := (57408611409863643733075194729976276988887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-3331867524270057734449715736086262750000000000)
      constant := (50534937887280335836271505787095183697063880183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99938809291533317791/100000000000000000000)
  centralHi := (3123087790360416181/3125000000000000000)
  directionLo := (27933746395782012037/25000000000000000000)
  directionHi := (111734985583128048149/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree006.table
  base := (8630355211277751815359832928523630927947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-23601755077890506705267856383991000000000000)
      constant := (242279072159826904565270561086331034239778335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree006.table
  base := (5382522596480174742816105769960608270951/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-443683164379027595996289256935143500000000000)
      constant := (4542818724485440066759268435774050376500322808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27933746395782012037/25000000000000000000)
  centralHi := (111734985583128048149/100000000000000000000)
  directionLo := (122399544132787517989/100000000000000000000)
  directionHi := (12239954413278751799/10000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree007.table
  base := (33627870741730258104510511040355321628331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-247592427590949983835502333560579000000000000)
      constant := (1891312844843104299176011708841168176452355019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree007.table
  base := (33558951042169301991733489597485675742243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-4654429434552438993483490888746320250000000000)
      constant := (35478106151269889099367030593991506831102897987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122399544132787517989/100000000000000000000)
  centralHi := (12239954413278751799/10000000000000000000)
  directionLo := (66103308927327090863/50000000000000000000)
  directionHi := (132206617854654181727/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree008.table
  base := (3355661212831649369829042351652376789331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-282769059480885407323593959665239000000000000)
      constant := (1737760134046276695931087818614813544368352152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree008.table
  base := (26790879224326565072217699751418567828647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-5315710389693629623000378465076349000000000000)
      constant := (32612172758595524360258964770431589442039834023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66103308927327090863/50000000000000000000)
  centralHi := (132206617854654181727/100000000000000000000)
  directionLo := (5653392780300188189/4000000000000000000)
  directionHi := (70667409753752352363/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree009.table
  base := (5425629403919267366673618032576136284957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-3925255449022479392736859083579000000000000)
      constant := (20650057863606708388425787838512104378969012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree009.table
  base := (1353599434182388727292406446327972820167/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-664110149426091139168585115711819750000000000)
      constant := (3489311826416903660026813362480834639844499472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5653392780300188189/4000000000000000000)
  centralHi := (70667409753752352363/50000000000000000000)
  directionLo := (149908213937299976687/100000000000000000000)
  directionHi := (9369263371081248543/6250000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree010.table
  base := (8805435735137186735372046953378030333561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-353122323260756254299777211874559000000000000)
      constant := (1670772025242611152710094438486180443525510578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree010.table
  base := (2196556240248907096266339100210044017223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-6638272299976010882034153617736406500000000000)
      constant := (31380994351726132289236780770722389109480246456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149908213937299976687/100000000000000000000)
  centralHi := (9369263371081248543/6250000000000000000)
  directionLo := (158017132003221933973/100000000000000000000)
  directionHi := (79008566001610966987/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree011.table
  base := (7121487710881625223136662564662047946261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-388298955150691677787868837979219000000000000)
      constant := (1718084421348907145455266581476187184898675178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree011.table
  base := (3552330776488038254121251036938602696607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-7299553255117201511551041194066435250000000000)
      constant := (32281326918444781092764770930634114778769546652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158017132003221933973/100000000000000000000)
  centralHi := (79008566001610966987/50000000000000000000)
  directionLo := (1035811038796562427/625000000000000000)
  directionHi := (165729766207449988321/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree012.table
  base := (2851693253126708237537852156340352740779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-47052843004514122363995607120431000000000000)
      constant := (200706938679749913847477269977637677595395276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree012.table
  base := (1137687304285333531940375959971488164973/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-884537134473154682340880974488496000000000000)
      constant := (3772316922090617615726504066537079009367511730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1035811038796562427/625000000000000000)
  centralHi := (165729766207449988321/100000000000000000000)
  directionLo := (21637386917609037587/12500000000000000000)
  directionHi := (173099095340872300697/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree013.table
  base := (4491028594307788199806671824247336460723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-458652218930562524764052090188539000000000000)
      constant := (1930455353497024294399283466472485240011039654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree013.table
  base := (2238823336877934086341284560716821841287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-51018432931358477932454534596014750000000000)
      constant := (214752504124631372848523093957335912957969628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21637386917609037587/12500000000000000000)
  centralHi := (173099095340872300697/100000000000000000000)
  directionLo := (180167250654720169073/100000000000000000000)
  directionHi := (90083625327360084537/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree014.table
  base := (1377639949168907663531715342139041242043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-493828850820497948252143716293199000000000000)
      constant := (2086908299563040814574233975088884890901502535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree014.table
  base := (6864172264741050377859196946797875622033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-9283396120540773400101703923056521500000000000)
      constant := (39243589591257513246095020938283210562618350097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180167250654720169073/100000000000000000000)
  centralHi := (90083625327360084537/50000000000000000000)
  directionLo := (93484196002764461579/50000000000000000000)
  directionHi := (186968392005528923159/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree015.table
  base := (1013500343259590054785205429920089194567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-58778386967825930193359482488651000000000000)
      constant := (252583215915603667075511667816262723276667435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree015.table
  base := (630740613157758125355931302952958968959/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-1104964119520218225513176833265172250000000000)
      constant := (4750640906802437158263922129812866948583728472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93484196002764461579/50000000000000000000)
  centralHi := (186968392005528923159/100000000000000000000)
  directionLo := (193530672012953797571/100000000000000000000)
  directionHi := (48382668003238449393/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree016.table
  base := (434550683824751986758358005588088524391/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-564182114600368795228326968502519000000000000)
      constant := (2487610883667991664870923516132176041453039672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree016.table
  base := (3457053029030849194320390438104382449591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-10605958030823154659135479075716579000000000000)
      constant := (46794709831532458247334753157239088058382964919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193530672012953797571/100000000000000000000)
  centralHi := (48382668003238449393/25000000000000000000)
  directionLo := (99938809291533317791/50000000000000000000)
  directionHi := (199877618583066635583/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree017.table
  base := (83227856872982130771569301135809669711/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-599358746490304218716418594607179000000000000)
      constant := (2728528060010773923538367303223980713436165975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree017.table
  base := (128960843571064219985563951466711363279/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-11267238985964345288652366652046607750000000000)
      constant := (51332910540973546448597753939363911370557346576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99938809291533317791/50000000000000000000)
  centralHi := (199877618583066635583/100000000000000000000)
  directionLo := (103014566701862886839/50000000000000000000)
  directionHi := (206029133403725773679/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree018.table
  base := (852756287578257419881080707234743676417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-7833770103459748669191484206319000000000000)
      constant := (36973050080077184698842650123949179404824593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree018.table
  base := (418643004313087416932262594542953905713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-1325391104567281768685472692041848500000000000)
      constant := (6260906982110506662934046899362184900499295826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103014566701862886839/50000000000000000000)
  centralHi := (206029133403725773679/100000000000000000000)
  directionLo := (212002229261257057087/100000000000000000000)
  directionHi := (3312534832207141517/1562500000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree019.table
  base := (-23010664893969203144089560508878386621/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-669712010270175065692601846816499000000000000)
      constant := (3285505555721313121728373285500601700116767710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree019.table
  base := (-121944558524812563121743637294298796463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-12589800896246726547686141804706665250000000000)
      constant := (61822218450509520444424973316231090524665904066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212002229261257057087/100000000000000000000)
  centralHi := (3312534832207141517/1562500000000000000)
  directionLo := (108905792559894357199/50000000000000000000)
  directionHi := (217811585119788714399/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree020.table
  base := (-1186744016198337083587956167603165680013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-704888642160110489180693472921159000000000000)
      constant := (3599785784287687426293374610191551953777122963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree020.table
  base := (-599496857802990820779779252015264175451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-13251081851387917177203029381036694000000000000)
      constant := (67739917064925127214673622191251864989109092682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108905792559894357199/50000000000000000000)
  centralHi := (217811585119788714399/100000000000000000000)
  directionLo := (223469971166256096297/100000000000000000000)
  directionHi := (111734985583128048149/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree021.table
  base := (-2032923710330838700110144052930166176903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-82229474894449545852087233225091000000000000)
      constant := (437442455955996117797122537610440478831764817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree021.table
  base := (-2043786463222978244988621556880045065993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-1545818089614345311857768550818524750000000000)
      constant := (8232064345506533271758362604083021723867659807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223469971166256096297/100000000000000000000)
  centralHi := (111734985583128048149/50000000000000000000)
  directionLo := (57247144805275931779/25000000000000000000)
  directionHi := (228988579221103727117/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree022.table
  base := (-2781888370041523903383348500696023271191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-775241905939981336156876725130479000000000000)
      constant := (4296527079844304314788773492379094098852736841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree022.table
  base := (-1395750358900827798281505066205479283841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-14573643761670298436236804533696751500000000000)
      constant := (80857556905543138713451941067278080444065953662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57247144805275931779/25000000000000000000)
  centralHi := (228988579221103727117/100000000000000000000)
  directionLo := (23437728305949803413/10000000000000000000)
  directionHi := (234377283059498034131/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree023.table
  base := (-688957409700777236136772618423318628391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9882)
      previous := (4941)
      next := (4941)
      square := (64321350469203334293544216770000000000000)
      linear := (-1531982113100031681748522403091000000000000)
      constant := (8842992414422068369945339637401555955501645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree023.table
  base := (-431659507021912461764935901179794685617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (185562)
      previous := (92781)
      next := (92781)
      square := (1207812025477262610623219181570000000000000)
      linear := (-28799479615900735474014540850712250000000000)
      constant := (166423227692064067304575075726319641077912344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23437728305949803413/10000000000000000000)
  centralHi := (234377283059498034131/100000000000000000000)
  directionLo := (239644846001336800549/100000000000000000000)
  directionHi := (4792896920026736011/2000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree024.table
  base := (-4031019885036811602875491937025388837709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-93955018857761353681451108593311000000000000)
      constant := (564536337687688852184510358178966123743667451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree024.table
  base := (-2019251513640433625199098948501850395877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-1766245074661408855030064409595201000000000000)
      constant := (10624668335560604701572105555171276145516400646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239644846001336800549/100000000000000000000)
  centralHi := (4792896920026736011/2000000000000000000)
  directionLo := (122399544132787517989/50000000000000000000)
  directionHi := (244799088265575035979/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree025.table
  base := (-181940772534311844095248519243547230881/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-880771801609787606621151603444459000000000000)
      constant := (5504839338871719837458906976661056117599500775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree025.table
  base := (-4555104515203107613096667338662362543063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-16557486627093870324787467262686837750000000000)
      constant := (103603564794533244755636587871002320019401122633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122399544132787517989/50000000000000000000)
  centralHi := (244799088265575035979/100000000000000000000)
  directionLo := (124923511614416647239/50000000000000000000)
  directionHi := (249847023228833294479/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree026.table
  base := (-500398266068206675916185545578063160137/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-915948433499723030109243229549119000000000000)
      constant := (5949692912502989405946784355597069716512896870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree026.table
  base := (-2504884249210611569999941129285314930391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-101886198711450064818368963544478500000000000)
      constant := (662586719318870570406438510647745137482816898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124923511614416647239/50000000000000000000)
  centralHi := (249847023228833294479/100000000000000000000)
  directionLo := (254794969371378151593/100000000000000000000)
  directionHi := (127397484685689075797/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree027.table
  base := (-1350766544538251855349434348146285268847/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-11742284757897017945646109329059000000000000)
      constant := (79199325868861302723624035964045460371119748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree027.table
  base := (-2704071108443392309187762440403698368609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-1986672059708472398202360268371877250000000000)
      constant := (13415360390113654869303427639478601682108473582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254794969371378151593/100000000000000000000)
  centralHi := (127397484685689075797/50000000000000000000)
  directionLo := (64912160752827112761/25000000000000000000)
  directionHi := (51929728602261690209/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree028.table
  base := (-5750547733405103730057044625705492302441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-986301697279593877085426481758439000000000000)
      constant := (6900992060645778106229348854323117360332705591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree028.table
  base := (-5754994968511701445241899977339657788293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-18541329492517442213338129991676924000000000000)
      constant := (129882991212910943522739308054250189161619357563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64912160752827112761/25000000000000000000)
  centralHi := (51929728602261690209/20000000000000000000)
  directionLo := (264413235709308363453/100000000000000000000)
  directionHi := (132206617854654181727/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree029.table
  base := (-6050463649387201359919350345561691759361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1021478329169529300573518107863099000000000000)
      constant := (7407059955904992074475560247667068069803140511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree029.table
  base := (-94599297176028980203756948796480176427/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-19202610447658632842855017568006952750000000000)
      constant := (139408157491499515423713093872512708750728369248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264413235709308363453/100000000000000000000)
  centralHi := (132206617854654181727/50000000000000000000)
  directionLo := (269093479331845999383/100000000000000000000)
  directionHi := (33636684916480749923/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree030.table
  base := (-3153112005399670712895746543743785441913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-117406106784384969340178859329751000000000000)
      constant := (881466995826232818180424763191001675022104414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree030.table
  base := (-6309624952239333016765120762341015277743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-2207099044755535941374656127148553500000000000)
      constant := (16590111621979008497844361080574684799404498057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269093479331845999383/100000000000000000000)
  centralHi := (33636684916480749923/12500000000000000000)
  directionLo := (273693701095898435723/100000000000000000000)
  directionHi := (68423425273974608931/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree031.table
  base := (-6520709933314633874344959222516108840587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1091831592949400147549701360072419000000000000)
      constant := (8479297627313610885569210197966566252289687637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree031.table
  base := (-3261839478042240500102763720510763629997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-20525172357941014101888792720667010250000000000)
      constant := (159589219933788252273626329872378346355675987654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273693701095898435723/100000000000000000000)
  centralHi := (68423425273974608931/25000000000000000000)
  directionLo := (139108935209266269429/50000000000000000000)
  directionHi := (278217870418532538859/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree032.table
  base := (-837044458843245215846040656130175358819/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1127008224839335571037792986177079000000000000)
      constant := (9045239645195910415736812921030032928399717352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree032.table
  base := (-3349472466605316003886589024093477812189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-21186453313082204731405680296997039000000000000)
      constant := (170240849987301371525972911018044919822024841798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139108935209266269429/50000000000000000000)
  centralHi := (278217870418532538859/100000000000000000000)
  directionLo := (5653392780300188189/2000000000000000000)
  directionHi := (282669639015009409451/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree033.table
  base := (-854402243806406951460720031327045207021/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-129131650747696777169542734697971000000000000)
      constant := (1070104543041381553846746001872028502154984152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree033.table
  base := (-273498952906663624108076416678648784237/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-2427526029802599484546951985925229750000000000)
      constant := (20140471617148146071868886459677317446323199075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5653392780300188189/2000000000000000000)
  centralHi := (282669639015009409451/100000000000000000000)
  directionLo := (287052375397814982539/100000000000000000000)
  directionHi := (14352618769890749127/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree034.table
  base := (-6939034537088348219297971921840889841693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1197361488619206418013976238386399000000000000)
      constant := (10236326892365358119278503361415325711173296643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree034.table
  base := (-6940998141716728590384929638964816460169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-22509015223364585990439455449657096500000000000)
      constant := (192658009635900512702201909873979550399049881079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287052375397814982539/100000000000000000000)
  centralHi := (14352618769890749127/5000000000000000000)
  directionLo := (145684597351762330023/50000000000000000000)
  directionHi := (291369194703524660047/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree035.table
  base := (-7009273704902503789531034715474064205297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1232538120509141841502067864491059000000000000)
      constant := (10861334746091547492293588590504966822867228847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree035.table
  base := (-7010981429441495621784708339974426367931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-23170296178505776619956343025987125250000000000)
      constant := (204420967655286984178907442091730381969837906021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145684597351762330023/50000000000000000000)
  centralHi := (291369194703524660047/100000000000000000000)
  directionLo := (9238218268698255049/3125000000000000000)
  directionHi := (295622984598344161569/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree036.table
  base := (-1409435206658100161650079697405244190181/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-15650799412334287222100734451799000000000000)
      constant := (142048287542770735090433593126647129116971255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree036.table
  base := (-7048660009580931662582467064524188236567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-2647953014849663027719247844701906000000000000)
      constant := (24061347095031619917798863734359478422462673633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9238218268698255049/3125000000000000000)
  centralHi := (295622984598344161569/100000000000000000000)
  directionLo := (149908213937299976687/50000000000000000000)
  directionHi := (2398531422996799627/800000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree037.table
  base := (-7053789718548830834786621083150406121587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1302891384289012688478251116700379000000000000)
      constant := (12170011612820895902547345646504441248096118637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree037.table
  base := (-3527539133714859135541769106406239768083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-24492858088788157878990118178647182750000000000)
      constant := (229050637914085729512102409229303105598197510906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149908213937299976687/50000000000000000000)
  centralHi := (2398531422996799627/800000000000000000)
  directionLo := (303952022240579216167/100000000000000000000)
  directionHi := (37994002780072402021/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree038.table
  base := (-7030000408499843619337459264095403824141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1338068016178948111966342742805039000000000000)
      constant := (12853597762537406708514038720823138041539382291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree038.table
  base := (-703111844890547666058375447803825197951/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-25154139043929348508507005754977211500000000000)
      constant := (241915799968684903647836602304491666019268438410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303952022240579216167/100000000000000000000)
  centralHi := (37994002780072402021/12500000000000000000)
  directionLo := (38504012214798377307/12500000000000000000)
  directionHi := (308032097718387018457/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree039.table
  base := (-6976556409964510123420642888726445476523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-152582738674320392828270485434411000000000000)
      constant := (1506293075101665575055014117721332393086273997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree039.table
  base := (-3488762916402716830301794863095143435469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-16972662721282405744920376943660250000000000)
      constant := (167749513715354598149453460800763721057773798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38504012214798377307/12500000000000000000)
  centralHi := (308032097718387018457/100000000000000000000)
  directionLo := (312058831993972405137/100000000000000000000)
  directionHi := (156029415996986202569/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree040.table
  base := (-53860078022934828547274435723306230123/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1408421279958818958942525995014359000000000000)
      constant := (14279104261073817629072726820770942572218825344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree040.table
  base := (-344746499742469825467695272658676355721/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-26476700954211729767540780907637269000000000000)
      constant := (268743762528903711542419140892354386521993638220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312058831993972405137/100000000000000000000)
  centralHi := (156029415996986202569/50000000000000000000)
  directionLo := (158017132003221933973/50000000000000000000)
  directionHi := (316034264006443867947/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree041.table
  base := (-6783135355831730940449911141441694580977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1443597911848754382430617621119019000000000000)
      constant := (15020974627374575182463247494532713828899716527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree041.table
  base := (-847982846299608288170885991206296851651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-27137981909352920397057668483967297750000000000)
      constant := (282705628552716234099748838562818561704732024328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158017132003221933973/50000000000000000000)
  centralHi := (316034264006443867947/100000000000000000000)
  directionLo := (319960306017398084187/100000000000000000000)
  directionHi := (79990076504349521047/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree042.table
  base := (-6644143890100851858455691231839925153719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-164308282637632200657634360802631000000000000)
      constant := (1753581048212931578887786300004432116343143841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree042.table
  base := (-6644773428433609362307784607951859145123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-3088806984943790114063839562255258500000000000)
      constant := (33003582994069171445492934285264614246816858677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319960306017398084187/100000000000000000000)
  centralHi := (79990076504349521047/25000000000000000000)
  directionLo := (323838754363030792637/100000000000000000000)
  directionHi := (161919377181515396319/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree043.table
  base := (-3238748483483613420258423109318091945163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1513951175628625229406800873328339000000000000)
      constant := (16562852339066564707368833880877965156483421226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree043.table
  base := (-809755186225830205215164329662716148691/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-28460543819635301656091443636627355250000000000)
      constant := (311723312344733441605678833210705514548855565448) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323838754363030792637/100000000000000000000)
  centralHi := (161919377181515396319/50000000000000000000)
  directionLo := (327671299060585655357/100000000000000000000)
  directionHi := (163835649530292827679/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree044.table
  base := (-3141758410989173369190768242010755992619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1549127807518560652894892499432999000000000000)
      constant := (17362829535354142239092962112830438232944536938) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree044.table
  base := (-6283987555449197620306055354519785915589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-29121824774776492285608331212957384000000000000)
      constant := (326778566788652641029414307802189277449243850299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327671299060585655357/100000000000000000000)
  centralHi := (163835649530292827679/50000000000000000000)
  directionLo := (1035811038796562427/312500000000000000)
  directionHi := (331459532414899976641/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree045.table
  base := (-6062475720298145284448258290159009012719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-19559314066771556498555359574539000000000000)
      constant := (224470979709742066773616274439010884232271649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree045.table
  base := (-6062882453547667928031732719446579243889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-3309233969990853657236135421031934750000000000)
      constant := (38021976929731546411361502345223496876829579511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1035811038796562427/312500000000000000)
  centralHi := (331459532414899976641/100000000000000000000)
  directionLo := (67040991349876828889/20000000000000000000)
  directionHi := (167602478374692072223/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree046.table
  base := (-5814603705777506308238753948434236099359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9882)
      previous := (4941)
      next := (4941)
      square := (64321350469203334293544216770000000000000)
      linear := (-3061400890923310963839462668511000000000000)
      constant := (35956147344654997532830860292562826875951921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree046.table
  base := (-1162990993326802298712475218009937361463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (185562)
      previous := (92781)
      next := (92781)
      square := (1207812025477262610623219181570000000000000)
      linear := (-57550825491604675887792261560713500000000000)
      constant := (676712296788361086356451866025495582616073885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67040991349876828889/20000000000000000000)
  centralHi := (167602478374692072223/50000000000000000000)
  directionLo := (16945449568395113949/5000000000000000000)
  directionHi := (338908991367902278981/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree047.table
  base := (-554009514835229087259216159175729759817/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1654657703188366923359167377746979000000000000)
      constant := (19878778973296919387025188478590934555216013670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree047.table
  base := (-5540398359067974349480216921218669130583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-31105667640200064174158993941947470250000000000)
      constant := (374127449186786701074812899194929116982323242953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16945449568395113949/5000000000000000000)
  centralHi := (338908991367902278981/100000000000000000000)
  directionLo := (21410811177440718859/6250000000000000000)
  directionHi := (68514595767810300349/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree048.table
  base := (-5239114276116575449535324343541807840773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-187759370564255816316362111539071000000000000)
      constant := (2306230378155864600265114464448925452870079747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree048.table
  base := (-261968794557295955135867478183243643249/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-3529660955037917200408431279808611000000000000)
      constant := (43404177062679020095355786867322869700997923020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21410811177440718859/6250000000000000000)
  centralHi := (68514595767810300349/20000000000000000000)
  directionLo := (21637386917609037587/6250000000000000000)
  directionHi := (346198190681744601393/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree049.table
  base := (-4911799849520784949477696986531889109133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1725010966968237770335350629956299000000000000)
      constant := (21652679289893539483963915471128116083562760083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree049.table
  base := (-1228006369289959697079767149975062602187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-32428229550482445433192769094607527750000000000)
      constant := (407511127165935887808795825531676934676680180468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21637386917609037587/6250000000000000000)
  centralHi := (346198190681744601393/100000000000000000000)
  directionLo := (34978583252036661227/10000000000000000000)
  directionHi := (349785832520366612271/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree050.table
  base := (-4558269110727986305809972435443916128303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1760187598858173193823442256060959000000000000)
      constant := (22568591609059748376729986551151613637818344753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree050.table
  base := (-4558463620305873984558334400926250266169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-33089510505623636062709656670937556500000000000)
      constant := (424747956252740678452050502001091334605838027079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34978583252036661227/10000000000000000000)
  centralHi := (349785832520366612271/100000000000000000000)
  directionLo := (353337048768761761813/100000000000000000000)
  directionHi := (176668524384380880907/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree051.table
  base := (-417862112053165551173875796206167314543/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-199484914527567624145725986907291000000000000)
      constant := (2611534012916163158650148167235795374154607770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree051.table
  base := (-1044697184177331670131637074306724527999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-3750087940084980743580727138585287250000000000)
      constant := (49149777959780598853313918653447733964701945604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353337048768761761813/100000000000000000000)
  centralHi := (176668524384380880907/50000000000000000000)
  directionLo := (44606615861829897363/12500000000000000000)
  directionHi := (71370585378927835781/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree052.table
  base := (-603670332449198518810442763441109101/1600000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1830540862638044040799625508270279000000000000)
      constant := (24458319225037574846214474626988987475820318750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree052.table
  base := (-3773083963404010543382353662748363051533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-203621730271633238590197821441406000000000000)
      constant := (2723734890112333619592906948432096418511651387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44606615861829897363/12500000000000000000)
  centralHi := (71370585378927835781/20000000000000000000)
  directionLo := (180167250654720169073/50000000000000000000)
  directionHi := (360334501309440338147/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree053.table
  base := (-3341295201744168768848603182465187439081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1865717494527979464287717134374939000000000000)
      constant := (25432127905189552020877722920074246183422818231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree053.table
  base := (-1670709765190238366794833784923252441529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-35073353371047207951260319399927642750000000000)
      constant := (478637484117935187167508809361404225747860085678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180167250654720169073/50000000000000000000)
  centralHi := (360334501309440338147/100000000000000000000)
  directionLo := (90945689230776431603/25000000000000000000)
  directionHi := (363782756923105726413/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree054.table
  base := (-2883747744654141571137437121650112962499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-23467828721208825775009984697279000000000000)
      constant := (326237402424377329591685782252033090242838029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree054.table
  base := (-90120461386878579020465666650368671897/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-3970514925132044286753022997361963500000000000)
      constant := (55258535218894193729284746334332161647889561696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90945689230776431603/25000000000000000000)
  centralHi := (363782756923105726413/100000000000000000000)
  directionLo := (367198632398362553967/100000000000000000000)
  directionHi := (22949914524897659623/6250000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree055.table
  base := (-1200173846325734765378323191942537178421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1936070758307850311263900386584259000000000000)
      constant := (27437622135313108501081561286804403448883677142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree055.table
  base := (-18753435793792821826294519419534863929/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-36395915281329589210294094552587700250000000000)
      constant := (516379154661374427500777632551486539509438258592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367198632398362553967/100000000000000000000)
  centralHi := (22949914524897659623/6250000000000000000)
  directionLo := (370583023135005687251/100000000000000000000)
  directionHi := (92645755783751421813/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree056.table
  base := (-378227540520007801275908994566963034553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-1971247390197785734751992012688919000000000000)
      constant := (28469303694201225766759968861500385004662192515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree056.table
  base := (-472804229410424120642896944135668515571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-37057196236470779839810982128917729000000000000)
      constant := (535794463128322431359289362312471669565419733044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370583023135005687251/100000000000000000000)
  centralHi := (92645755783751421813/25000000000000000000)
  directionLo := (93484196002764461579/25000000000000000000)
  directionHi := (373936784011057846317/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree057.table
  base := (-169519227028684394308445540670330882371/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-222936002454191239804453737643731000000000000)
      constant := (3280030303187426976181395023429385437352253352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree057.table
  base := (-1356221935386114988541068278343132784719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-4190941910179107829925318856138639750000000000)
      constant := (61730301510638075284111312302368178406225836681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93484196002764461579/25000000000000000000)
  centralHi := (373936784011057846317/100000000000000000000)
  directionLo := (94315182976146824871/25000000000000000000)
  directionHi := (75452146380917459897/20000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree058.table
  base := (-795426485974004873113779566795875353857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2041600653977656581728175264898239000000000000)
      constant := (30590527933913605369342930158851505536962581407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree058.table
  base := (-795485045449849450624439151750059115727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-38379758146753161098844757281577786500000000000)
      constant := (575713881755905569284140916520662343841204014257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94315182976146824871/25000000000000000000)
  centralHi := (75452146380917459897/20000000000000000000)
  directionLo := (190277824008630377813/50000000000000000000)
  directionHi := (380555648017260755627/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree059.table
  base := (-41796288346189576304656290004799453789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2076777285867592005216266891002899000000000000)
      constant := (31680068207381143265242874771790932741022975695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree059.table
  base := (-52257942036088821993896952401318530999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-39041039101894351728361644857907815250000000000)
      constant := (596217947074938826707356689513158639312678202436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190277824008630377813/50000000000000000000)
  centralHi := (380555648017260755627/100000000000000000000)
  directionLo := (11994446250573638967/3125000000000000000)
  directionHi := (76764456003671289389/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree060.table
  base := (16126383071683781795576868873053732771/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-234661546417503047633817613011951000000000000)
      constant := (3643210290840525051809128087044675220543068275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree060.table
  base := (80623267670689921478356386592703964623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-4411368895226171373097614714915316000000000000)
      constant := (68564988022993253122052652831757378510706304115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11994446250573638967/3125000000000000000)
  centralHi := (76764456003671289389/20000000000000000000)
  directionLo := (193530672012953797571/50000000000000000000)
  directionHi := (387061344025907595143/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree061.table
  base := (1040978201297784185689292752712859438519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2147130549647462852192450143212219000000000000)
      constant := (33917000377401179327053343284871722314081100631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree061.table
  base := (1040941062882117537889787015991028002957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-40363601012176732987395420010567872750000000000)
      constant := (638314702499042522186983985437640029870743728813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193530672012953797571/50000000000000000000)
  centralHi := (387061344025907595143/100000000000000000000)
  directionLo := (19513676321992375903/5000000000000000000)
  directionHi := (390273526439847518061/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree062.table
  base := (1704458912076025041881485490256179777943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2182307181537398275680541769316879000000000000)
      constant := (35064390821886446944095516113416565047305079607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree062.table
  base := (426106755418140937996560726200377842187/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-41024881967317923616912307586897901500000000000)
      constant := (659907365573329499460041459902368597417146959532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19513676321992375903/5000000000000000000)
  centralHi := (390273526439847518061/100000000000000000000)
  directionLo := (393459485640449042533/100000000000000000000)
  directionHi := (196729742820224521267/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree063.table
  base := (2393588596257111870412311468237173065093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-27376343375646095051464609820019000000000000)
      constant := (447297078878360176758630416937624464551434197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree063.table
  base := (598390304848856545686174955032247005453/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-4631795880273234916269910573691992250000000000)
      constant := (75762541219293471914925625439950742978450514612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393459485640449042533/100000000000000000000)
  centralHi := (196729742820224521267/50000000000000000000)
  directionLo := (396619853563962545179/100000000000000000000)
  directionHi := (19830992678198127259/5000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree064.table
  base := (1554178087284153957792619505681448431999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2252660445317269122656725021526199000000000000)
      constant := (37417017604447603949869145574710144767725450302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree064.table
  base := (97135396198594154643459778123223702521/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-42347443877600304875946082739557959000000000000)
      constant := (704181209867225012560709760103210960801975017248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396619853563962545179/100000000000000000000)
  centralHi := (19830992678198127259/5000000000000000000)
  directionLo := (79951047433226654233/20000000000000000000)
  directionHi := (199877618583066635583/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree065.table
  base := (481094035746350329521866900003188673399/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2287837077207204546144816647630859000000000000)
      constant := (38622253066676583848474797231431978051731790008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree065.table
  base := (3848732125250253949684435020431694559381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-254489496051724825476112250389869750000000000)
      constant := (4300960797589936655190632034194602993109712941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79951047433226654233/20000000000000000000)
  centralHi := (199877618583066635583/50000000000000000000)
  directionLo := (100716554945799447367/25000000000000000000)
  directionHi := (402866219783197789469/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree066.table
  base := (4614769021201347381399786913700556820609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-258112634344126663292545363748391000000000000)
      constant := (4427418826325565896869853044612414351022919449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree066.table
  base := (4614751726565522633509203871992013079559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-4852222865320298459442206432468668500000000000)
      constant := (83322928827460768774339767871368944117575654159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100716554945799447367/25000000000000000000)
  centralHi := (402866219783197789469/100000000000000000000)
  directionLo := (202976681199501456741/50000000000000000000)
  directionHi := (405953362399002913483/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree067.table
  base := (1351599924408688883408410937061323899927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2358190340987075393120999899840179000000000000)
      constant := (41090566428864324998552123166282285671151888092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree067.table
  base := (5406384865041658504998352739976701874207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-44331286743023876764496745468548045250000000000)
      constant := (773313158506261609419457955654902994813616320063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202976681199501456741/50000000000000000000)
  centralHi := (405953362399002913483/100000000000000000000)
  directionLo := (409017204826042200393/100000000000000000000)
  directionHi := (204508602413021100197/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree068.table
  base := (6223638669059498230485183116458618063123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2393366972877010816609091525944839000000000000)
      constant := (42353643800544761828420528744204667325386757427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree068.table
  base := (1555906487712396463037986386925255829919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-44992567698165067394013633044878074000000000000)
      constant := (797082767472416583298860391649910169047221186684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409017204826042200393/100000000000000000000)
  centralHi := (204508602413021100197/50000000000000000000)
  directionLo := (103014566701862886839/25000000000000000000)
  directionHi := (412058266807451547357/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree069.table
  base := (7066481164952298887180390381944225286319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (1098)
      previous := (549)
      next := (549)
      square := (7146816718800370477060468530000000000000)
      linear := (-510091074305176693992266992659000000000000)
      constant := (9165301690308601487723779118278498027576871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree069.table
  base := (7066470262079029543560815345851941989267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (20618)
      previous := (10309)
      next := (10309)
      square := (134201336164140290069246575730000000000000)
      linear := (-9589130151923179589063331363412750000000000)
      constant := (172487961047326262559138252555644236008686123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103014566701862886839/25000000000000000000)
  centralHi := (412058266807451547357/100000000000000000000)
  directionLo := (415077049046334639871/100000000000000000000)
  directionHi := (1621394722837244687/390625000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree070.table
  base := (158698463093544206800046019138320032627/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2463720236656881663585274778154159000000000000)
      constant := (44937638897199074862431165864418023753901716150) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree070.table
  base := (3967456904995611631127246087022880729969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-46315129608447448653047408197538131500000000000)
      constant := (845710400518597757627517149093084744988769254242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415077049046334639871/100000000000000000000)
  centralHi := (1621394722837244687/390625000000000000)
  directionLo := (418074034168190907899/100000000000000000000)
  directionHi := (4180740341681909079/1000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree071.table
  base := (8828961232744042899194740987599005052863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2498896868546817087073366404258819000000000000)
      constant := (46258556303542382228538926897626548767510126687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree071.table
  base := (8828953225191052297057302105562809513717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-46976410563588639282564295773868160250000000000)
      constant := (870568418678203214196595829854393792357834821653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418074034168190907899/100000000000000000000)
  centralHi := (4180740341681909079/1000000000000000000)
  directionLo := (210524843810842207021/50000000000000000000)
  directionHi := (421049687621684414043/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree072.table
  base := (4874296260930194897788119258174305070681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-31284858030083364327919234942759000000000000)
      constant := (587638931398766314120043686294276414764780498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree072.table
  base := (4874292830735465236383008933791588174301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-5293076835414425545786798150022021000000000000)
      constant := (99532137192783607338494352134288110548741367402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210524843810842207021/50000000000000000000)
  centralHi := (421049687621684414043/100000000000000000000)
  directionLo := (16960178340900564567/4000000000000000000)
  directionHi := (3312534832207141517/781250000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree073.table
  base := (10693814591017927396751038469222575160049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2569250132326687934049549656468139000000000000)
      constant := (48958230212305866848660475231884195123032939601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree073.table
  base := (2138761742916581576905302217166735998429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-48298972473871020541598070926528217750000000000)
      constant := (921372846754665974452082391778586782057612296305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16960178340900564567/4000000000000000000)
  centralHi := (3312534832207141517/781250000000000000)
  directionLo := (53367347555589696927/12500000000000000000)
  directionHi := (426938780444717575417/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree074.table
  base := (11664625386281564746217363234938116770271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2604426764216623357537641282572799000000000000)
      constant := (50336986522550703730954592154904109365489342079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree074.table
  base := (11664620353621428045875279851870137228403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-48960253429012211171114958502858246500000000000)
      constant := (947319253102958850514478585757323787901458109427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53367347555589696927/12500000000000000000)
  centralHi := (426938780444717575417/100000000000000000000)
  directionLo := (42985307216335574881/10000000000000000000)
  directionHi := (429853072163355748811/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree075.table
  base := (12661023172311558879339989171872318419739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-293289266234062086780636989853051000000000000)
      constant := (5748335811075223271590470517897359107996377379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree075.table
  base := (3165254715764737959682517809965592063159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-5513503820461489088959094008798697250000000000)
      constant := (108180939155511355167930745300044968591966411036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42985307216335574881/10000000000000000000)
  centralHi := (429853072163355748811/100000000000000000000)
  directionLo := (21637386917609037587/5000000000000000000)
  directionHi := (432747738352180751741/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree076.table
  base := (13683006482954188889653926552081420885563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2674780027996494204513824534782119000000000000)
      constant := (53152337480861563201618284405547900803525488987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree076.table
  base := (6841501396890303343414956828460195189517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-50282815339294592430148733655518304000000000000)
      constant := (1000300443478625143934063993515445954257484167706) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21637386917609037587/5000000000000000000)
  centralHi := (432747738352180751741/100000000000000000000)
  directionLo := (108905792559894357199/25000000000000000000)
  directionHi := (435623170239577428797/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree077.table
  base := (14730574079494687071848193555666652430003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2709956659886429628001916160886779000000000000)
      constant := (54588932013026675921461871128318273389973198547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree077.table
  base := (7365285460860387203878550336905635536267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-50944096294435783059665621231848332750000000000)
      constant := (1027335225355133479802403514850128818076713009206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108905792559894357199/25000000000000000000)
  centralHi := (435623170239577428797/100000000000000000000)
  directionLo := (109619936556447222007/25000000000000000000)
  directionHi := (438479746225788888029/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree078.table
  base := (15803724915384205633808457775367047263171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-305014810197373894610000865221271000000000000)
      constant := (6227200650147641780533409755563180512019957131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree078.table
  base := (3950930553230356429413043522791600520823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-33928584647979601373558519926481500000000000)
      constant := (693446940958050800875962128140774182952061468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109619936556447222007/25000000000000000000)
  centralHi := (438479746225788888029/100000000000000000000)
  directionLo := (1765271329856731531/400000000000000000)
  directionHi := (441317832464182882751/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree079.table
  base := (8451229053218429634210475679941549757577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2780309923666300474978099413096099000000000000)
      constant := (57519958957881382512110216582138621931124833746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree079.table
  base := (845122789700761579675396181499961606793/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-52266658204718164318699396384508390250000000000)
      constant := (1082493158302091295685995831216047006802414678740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1765271329856731531/400000000000000000)
  centralHi := (441317832464182882751/100000000000000000000)
  directionLo := (444137783409086867233/100000000000000000000)
  directionHi := (222068891704543433617/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree080.table
  base := (18026772905648571617515913351755069544767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2815486555556235898466191039200759000000000000)
      constant := (59014391300676117715519241387262072974923721183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree080.table
  base := (18026770927291259164133444353614810614657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-52927939159859354948216283960838419000000000000)
      constant := (1110616308076252706476819774961708054153848554113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444137783409086867233/100000000000000000000)
  centralHi := (222068891704543433617/50000000000000000000)
  directionLo := (223469971166256096297/50000000000000000000)
  directionHi := (89387988466502438519/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree081.table
  base := (4794167170480249601730366626315647082543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-35193372684520633604373860065499000000000000)
      constant := (747260529045321588657083598115272909226660988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree081.table
  base := (19176666989631808469324803803974306396551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-5954357790555616175303685726352049750000000000)
      constant := (126566916224257043450836722471996723161470555951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223469971166256096297/50000000000000000000)
  centralHi := (89387988466502438519/20000000000000000000)
  directionLo := (449724641811899930061/100000000000000000000)
  directionHi := (224862320905949965031/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree082.table
  base := (20352144902084945707877061058972450799167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2885839819336106745442374291410079000000000000)
      constant := (62061093591020408618570345965636068544293506783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree082.table
  base := (318002241479990573422352775996882690731/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-54250501070141736207250059113498476500000000000)
      constant := (1167950971704793565901815346606334257140258267456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449724641811899930061/100000000000000000000)
  centralHi := (224862320905949965031/50000000000000000000)
  directionLo := (226246102095425092299/50000000000000000000)
  directionHi := (452492204190850184599/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree083.table
  base := (21553201115711611730082487404849219607213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2921016451226042168930465917514739000000000000)
      constant := (63613363496423773799646391260664251210949469837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree083.table
  base := (21553199878006199668485555842913020173503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-54911782025282926836766946689828505250000000000)
      constant := (1197162484778006050740194557111349380694094575327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226246102095425092299/50000000000000000000)
  centralHi := (452492204190850184599/100000000000000000000)
  directionLo := (7113170968978776541/1562500000000000000)
  directionHi := (3641943536117133589/800000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree084.table
  base := (22779836942279327570963291846119386458231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-328465898123997510268728615957711000000000000)
      constant := (7242768061397352359293943840663178398927637791) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree084.table
  base := (355934935687766849136160152313431180191/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-6174784775602679718475981585128726000000000000)
      constant := (136304087215093352158942750984609749275176357824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7113170968978776541/1562500000000000000)
  centralHi := (3641943536117133589/800000000000000000)
  directionLo := (457977158442207454233/100000000000000000000)
  directionHi := (228988579221103727117/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree085.table
  base := (24032052060330514751968405434973132400097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-2991369715005913015906649169724059000000000000)
      constant := (66775740745703465140340221128204428750211756353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree085.table
  base := (24032051155623899983574157266595645250097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-56234343935565308095800721842488562750000000000)
      constant := (1256673871923131772213554197374396508224347797073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457977158442207454233/100000000000000000000)
  centralHi := (228988579221103727117/50000000000000000000)
  directionLo := (230347573818051726523/50000000000000000000)
  directionHi := (460695147636103453047/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree086.table
  base := (2530984619831022327984360062752700464847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3026546346895848439394740795828719000000000000)
      constant := (68385848064169797467469620551343858622182291030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree086.table
  base := (3163730678123138564877795397053780905921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-56895624890706498725317609418818591500000000000)
      constant := (1286973745524373132504660148676144320213707519112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230347573818051726523/50000000000000000000)
  centralHi := (460695147636103453047/100000000000000000000)
  directionLo := (463397195131890632783/100000000000000000000)
  directionHi := (28962324695743164549/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree087.table
  base := (13306609563412737798071731918349294755123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-340191442087309318098092491325931000000000000)
      constant := (7779470499793989835514651700954888984658281206) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree087.table
  base := (665330461647300300155667484709759073359/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-6395211760649743261648277443905402250000000000)
      constant := (146404045061950522320751460759185527782007218360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463397195131890632783/100000000000000000000)
  centralHi := (28962324695743164549/6250000000000000000)
  directionLo := (466083578188242854259/100000000000000000000)
  directionHi := (23304178909412142713/5000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree088.table
  base := (27942170652105081327884485935824732567477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3096899610675719286370924048038039000000000000)
      constant := (71663900039328896560534985017386465965783821973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree088.table
  base := (13971085043651695882603820966450417432163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-58218186800988879984351384571478649000000000000)
      constant := (1348661851868962993438983547042336899839350478534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466083578188242854259/100000000000000000000)
  centralHi := (23304178909412142713/5000000000000000000)
  directionLo := (468754566118996068261/100000000000000000000)
  directionHi := (234377283059498034131/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree089.table
  base := (2929670061047375619107626200381501895917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3132076242565654709859015674142699000000000000)
      constant := (73331844680705439333894274817257450747381475330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree089.table
  base := (29296700127883943555433185205202186944419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-58879467756130070613868272147808677750000000000)
      constant := (1380050084328786172351651132807505852317974527171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468754566118996068261/100000000000000000000)
  centralHi := (234377283059498034131/50000000000000000000)
  directionLo := (471410420608264262449/100000000000000000000)
  directionHi := (9428208412165285249/2000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree090.table
  base := (30676808863683248208275600796290742110419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-39101887338957902880828485188239000000000000)
      constant := (926161338473478240626274955636747802576411651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree090.table
  base := (15338404225695351502972148083228444453731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-6615638745696806804820573302682078500000000000)
      constant := (156866789203044658033912547501536731231466010262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471410420608264262449/100000000000000000000)
  centralHi := (9428208412165285249/2000000000000000000)
  directionLo := (1481410612530205631/312500000000000000)
  directionHi := (474051396009665801921/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree091.table
  base := (16041247647483783628551659319819918414317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3202429506345525556835198926352019000000000000)
      constant := (76725571241264485120283149144113226368270138266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree091.table
  base := (32082494942775802820199385554440682994389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-356225027611907999247941108286797250000000000)
      constant := (8543875190960010022734117748914923599548786029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1481410612530205631/312500000000000000)
  centralHi := (474051396009665801921/100000000000000000000)
  directionLo := (119169434907657151193/25000000000000000000)
  directionHi := (476677739630628604773/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree092.table
  base := (33513759805710024124933630063972631830419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9882)
      previous := (4941)
      next := (4941)
      square := (64321350469203334293544216770000000000000)
      linear := (-6120238446569869528021343199351000000000000)
      constant := (148301234690393300012262959826593783178263939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree092.table
  base := (83784398762235870733685729022024716847/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (185562)
      previous := (92781)
      next := (92781)
      square := (1207812025477262610623219181570000000000000)
      linear := (-115053517243012556715347702980716000000000000)
      constant := (2790910203374559225668689311712763712729714800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119169434907657151193/25000000000000000000)
  centralHi := (476677739630628604773/100000000000000000000)
  directionLo := (239644846001336800549/50000000000000000000)
  directionHi := (479289692002673601099/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree093.table
  base := (17485301156313599650704436489835201342223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-363642530013932933756820242062371000000000000)
      constant := (8910712682515982000748980639573683787180647406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree093.table
  base := (4371325256965432947013031950287485209257/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-6836065730743870347992869161458754750000000000)
      constant := (167692319300011776422300250516370518979354780456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239644846001336800549/50000000000000000000)
  centralHi := (479289692002673601099/100000000000000000000)
  directionLo := (24094374356925627041/5000000000000000000)
  directionHi := (481887487138512540821/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree094.table
  base := (18226511372694837662778445174209463943311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3307959402015331827299473804665999000000000000)
      constant := (81960754212528286812259113210863628641013866078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree094.table
  base := (36453022526013146508005003210795652323867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-62185872531836023761452710029458821500000000000)
      constant := (1542433035561414991119939477940818230176904303003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24094374356925627041/5000000000000000000)
  centralHi := (481887487138512540821/100000000000000000000)
  directionLo := (242235676388368965621/50000000000000000000)
  directionHi := (484471352776737931243/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree095.table
  base := (18980510522305899194823639182824443072071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3343136033905267250787565430770659000000000000)
      constant := (83744373358326786243034528039747544122390340558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree095.table
  base := (37961020857301890880754901050107154343161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-62847153486977214390969597605788850250000000000)
      constant := (1575997983122030186287596393760882914731708929049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242235676388368965621/50000000000000000000)
  centralHi := (484471352776737931243/100000000000000000000)
  directionLo := (487041510614829239273/100000000000000000000)
  directionHi := (243520755307414619637/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree096.table
  base := (39494597160153238918852126094268033726543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-375368073977244741586184117430591000000000000)
      constant := (9505252397543430368568363231896826108572071223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree096.table
  base := (19747298500120221595059603795088268191591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-7056492715790933891165165020235431000000000000)
      constant := (178880635149138302198987132328863378529192853982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487041510614829239273/100000000000000000000)
  centralHi := (243520755307414619637/50000000000000000000)
  directionLo := (122399544132787517989/25000000000000000000)
  directionHi := (489598176531150071957/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree097.table
  base := (8210750209936799191173024708782161313257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3413489297685138097763748682979979000000000000)
      constant := (87369448869406749823481718276058127150558745965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree097.table
  base := (41053750913175853286106098333854223176393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-64169715397259595650003372758448907750000000000)
      constant := (1644216235188544253062568097620653683663546895337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122399544132787517989/25000000000000000000)
  centralHi := (489598176531150071957/100000000000000000000)
  directionLo := (15379423774892671221/3125000000000000000)
  directionHi := (492141560796565479073/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree098.table
  base := (21319241338735994491766747535604192670067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3448665929575073521251840309084639000000000000)
      constant := (89210905231343331844054396323164910103439401766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree098.table
  base := (21319241280477702834378722204734009838227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-64830996352400786279520260334778936500000000000)
      constant := (1678869539632644594836942303630225452250101976486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15379423774892671221/3125000000000000000)
  centralHi := (492141560796565479073/100000000000000000000)
  directionLo := (247335934138133233269/50000000000000000000)
  directionHi := (494671868276266466539/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree099.table
  base := (44248792013358716745316525796038090379737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-43010401993395172157283110310979000000000000)
      constant := (1124341242745782194549281359709795149810880873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree099.table
  base := (4424879191391629242992163931129657328857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-7276919700837997434337460879012107250000000000)
      constant := (190431736627853198100648539225502640081383946570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247335934138133233269/50000000000000000000)
  centralHi := (494671868276266466539/100000000000000000000)
  directionLo := (497189298622349964961/100000000000000000000)
  directionHi := (248594649311174982481/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree100.table
  base := (45884679031893816004900357175876408624409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3519019193354944368228023561293959000000000000)
      constant := (92951655161511304952481087191355028233147301241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree100.table
  base := (45884678947032189019132536541106940717317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-66153558262683167538554035487438994000000000000)
      constant := (1749264505222510411299025730150751898838619714053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497189298622349964961/100000000000000000000)
  centralHi := (248594649311174982481/50000000000000000000)
  directionLo := (499694046457666588957/100000000000000000000)
  directionHi := (249847023228833294479/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree101.table
  base := (11886535927900969097448900249089055056861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3554195825244879791716115187398619000000000000)
      constant := (94850948727732059264971489692152356680525747956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree101.table
  base := (23773071819596185669351063223201232820711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-66814839217824358168070923063769022750000000000)
      constant := (1785006166331153601410992283235424184422591413998) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499694046457666588957/100000000000000000000)
  centralHi := (249847023228833294479/50000000000000000000)
  directionLo := (502186301551415300921/100000000000000000000)
  directionHi := (251093150775707650461/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree102.table
  base := (12308296508593672307085137639918664650649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-398819161903868357244911868167031000000000000)
      constant := (10752169040032716107621218352065693049606959556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree102.table
  base := (24616592986296397447723059466346074847339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-7497346685885060977509756737788783500000000000)
      constant := (202345623662475895422902221534989145531103907878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502186301551415300921/100000000000000000000)
  centralHi := (251093150775707650461/50000000000000000000)
  directionLo := (252333124493466666039/50000000000000000000)
  directionHi := (504666248986933332079/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree103.table
  base := (50945805984929337390324377926408971327773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3624549089024750638692298439607939000000000000)
      constant := (98707373058543861441227109854295345012423745277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree103.table
  base := (12736451483055437942004538275685027787721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-68137401128106739427104698216429080250000000000)
      constant := (1857577845103820228185522287794022209350814124356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252333124493466666039/50000000000000000000)
  centralHi := (504666248986933332079/100000000000000000000)
  directionLo := (50713406932210120937/10000000000000000000)
  directionHi := (507134069322101209371/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree104.table
  base := (3292750221899203842836794499976940428983/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3659725720914686062180390065712599000000000000)
      constant := (100664503821928389593562457906132406727063881072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree104.table
  base := (52684003505425420150154993719451570142319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-407092793391999586133855537235261000000000000)
      constant := (11209513980743098997866766329774557925447580759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50713406932210120937/10000000000000000000)
  centralHi := (507134069322101209371/100000000000000000000)
  directionLo := (509589938742756303187/100000000000000000000)
  directionHi := (127397484685689075797/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree105.table
  base := (10889555743978348603015264658792230741403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-410544705867180165074275743535251000000000000)
      constant := (11404545961109203321628512833098154052799098415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree105.table
  base := (54447778681540901209285053028708065068231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-7717773670932124520682052596565459750000000000)
      constant := (214622296208777122422358562997475894295477419631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509589938742756303187/100000000000000000000)
  centralHi := (127397484685689075797/25000000000000000000)
  directionLo := (512034029209483779291/100000000000000000000)
  directionHi := (128008507302370944823/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree106.table
  base := (56237131484295192826299646260148877144911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3730078984694556909156573317921919000000000000)
      constant := (104636602542315217296888933533328453236782291439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree106.table
  base := (56237131451586264009641839280560171601649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-70121243993530311315655360945419166500000000000)
      constant := (1969156254496824399202456818369735430768481200241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512034029209483779291/100000000000000000000)
  centralHi := (128008507302370944823/25000000000000000000)
  directionLo := (514466508598131054899/100000000000000000000)
  directionHi := (5144665085981310549/1000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree107.table
  base := (2322082473435731156550456944207585516627/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3765255616584492332644664944026579000000000000)
      constant := (106651570498595428878164429834719653795048758075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree107.table
  base := (29026030903999373121333421933519005818901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-70782524948671501945172248521749195250000000000)
      constant := (2007074628592989556224845810856707400076192729418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514466508598131054899/100000000000000000000)
  centralHi := (5144665085981310549/1000000000000000000)
  directionLo := (516887540834370683897/100000000000000000000)
  directionHi := (258443770417185341949/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree108.table
  base := (59892569768200318107205691413802377296321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-46918916647832441433737735433719000000000000)
      constant := (1341800216278340241979269217336433457589753809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree108.table
  base := (59892569744413632907087024986923950050901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-7938200655979188063854348455342136000000000000)
      constant := (227261754240263162877326082616395892933500600301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516887540834370683897/100000000000000000000)
  centralHi := (258443770417185341949/50000000000000000000)
  directionLo := (64912160752827112761/12500000000000000000)
  directionHi := (519297286022616902089/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree109.table
  base := (15439663818939882758316075935272052598527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3835608880364363179620848196235899000000000000)
      constant := (110739343601931791923988612156329849727177133692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree109.table
  base := (61758655255477496101684774739509457312931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-72105086858953883204206023674409252750000000000)
      constant := (2083999733200653711945552818166921150509412598979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64912160752827112761/12500000000000000000)
  centralHi := (519297286022616902089/100000000000000000000)
  directionLo := (5216959005695827339/1000000000000000000)
  directionHi := (521695900569582733901/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree110.table
  base := (63650318353982752400689184542697355418571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3870785512254298603108939822340559000000000000)
      constant := (112812148748557527554603157680531528982330348779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree110.table
  base := (12730063667338091972489247731574796788663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-72766367814095073833722911250739281500000000000)
      constant := (2123006463704224653674170811286007266002896738835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5216959005695827339/1000000000000000000)
  centralHi := (521695900569582733901/100000000000000000000)
  directionLo := (524083537302747490959/100000000000000000000)
  directionHi := (6551044216284343637/1250000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree111.table
  base := (32783779499507513687951997349734594921249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-433995793793803780733003494271691000000000000)
      constant := (12767136995361953948055614513548803812840132978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree111.table
  base := (65567558984272982476567853376084557924079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-8158627641026251607026644314118812250000000000)
      constant := (240263997741115581978199062287613491133283086679) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524083537302747490959/100000000000000000000)
  centralHi := (6551044216284343637/1250000000000000000)
  directionLo := (131615086395997145821/25000000000000000000)
  directionHi := (105292069116797716657/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree112.table
  base := (67510377207620233465586734631480414887341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3941138776034169450085123074549879000000000000)
      constant := (117015596230893301244964376620552832297507674509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree112.table
  base := (33755188597526674289162382269753455916527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-74088929724377455092756686403399339000000000000)
      constant := (2202108281095548473605714556737035689823081745886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131615086395997145821/25000000000000000000)
  centralHi := (105292069116797716657/20000000000000000000)
  directionLo := (264413235709308363453/50000000000000000000)
  directionHi := (528826471418616726907/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree113.table
  base := (69478772977084466074907469413057808720961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-3976315407924104873573214700654539000000000000)
      constant := (119146238566348386594010827794742151045884457889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree113.table
  base := (69478772966372654545647117266829045157861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-74750210679518645722273573979729367750000000000)
      constant := (2242203367978609983295489795865352507453233881349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264413235709308363453/50000000000000000000)
  centralHi := (528826471418616726907/100000000000000000000)
  directionLo := (53118205756003978613/10000000000000000000)
  directionHi := (531182057560039786131/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree114.table
  base := (8934093288141803975832884793923083668081/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-445721337757115588562367369639911000000000000)
      constant := (13477351107169492581207014180660076410749869128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree114.table
  base := (71472746296004570140746734676899279296941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-8379054626073315150198940172895488500000000000)
      constant := (253629026701937049058535641195700589124675822341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53118205756003978613/10000000000000000000)
  centralHi := (531182057560039786131/100000000000000000000)
  directionLo := (4268217948882140481/800000000000000000)
  directionHi := (266763621805133780063/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree115.table
  base := (18373074297467130251893335327552229247967/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9882)
      previous := (4941)
      next := (4941)
      square := (64321350469203334293544216770000000000000)
      linear := (-7649657224393148810112283464771000000000000)
      constant := (233393876040345858380884446052041922276341308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree115.table
  base := (18373074295521895305919449243336679019927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15210000000000000000000000000000000000000000
      center := (185562)
      previous := (92781)
      next := (92781)
      square := (1207812025477262610623219181570000000000000)
      linear := (-143804863118716497129125423690717250000000000)
      constant := (4392215308337468917332854093202941175469735868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4268217948882140481/800000000000000000)
  centralHi := (266763621805133780063/50000000000000000000)
  directionLo := (33491385382278608983/6250000000000000000)
  directionHi := (535862166116457743729/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree116.table
  base := (37768712814849296110049436685733260693107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-4081845303593911144037489578968519000000000000)
      constant := (125653839948732913878570955697156492974877883686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree116.table
  base := (75537425623067774752331979270614541657293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-76734053544942217610824236708719454000000000000)
      constant := (2364665341356622538103369192316661264123332863437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33491385382278608983/6250000000000000000)
  centralHi := (535862166116457743729/100000000000000000000)
  directionLo := (269093479331845999383/50000000000000000000)
  directionHi := (538186958663691998767/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree117.table
  base := (77608131623300806341234583178605133487249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-50827431302269710710192360556459000000000000)
      constant := (1578538253514056449807255724361515115614754721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree117.table
  base := (38804065808825264167598766699173075550437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-50884506574676797002196662909302750000000000)
      constant := (1581993142705257211835553600009611434244862346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269093479331845999383/50000000000000000000)
  centralHi := (538186958663691998767/100000000000000000000)
  directionLo := (540501751964160507219/100000000000000000000)
  directionHi := (27025087598208025361/5000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree118.table
  base := (19926103792393526527396235287649024876323/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-4152198567373781991013672831177839000000000000)
      constant := (130088636183012755548344608842891374267702256908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree118.table
  base := (79704415164759720914637253155839546143541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-78056615455224598869858011861379511500000000000)
      constant := (2448120584203876243876538900354288429789258380469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540501751964160507219/100000000000000000000)
  centralHi := (27025087598208025361/5000000000000000000)
  directionLo := (271403336971461744257/50000000000000000000)
  directionHi := (108561334788584697703/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree119.table
  base := (81826276267605154377454094435108024234911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-4187375199263717414501764457282499000000000000)
      constant := (132334952893816327637000021607112894730441701439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree119.table
  base := (16365255252700659197038537028849541547557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-78717896410365789499374899437709540250000000000)
      constant := (2490392383803444855434554395804876677883003951065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271403336971461744257/50000000000000000000)
  centralHi := (108561334788584697703/20000000000000000000)
  directionLo := (27255092491020445069/5000000000000000000)
  directionHi := (545101849820408901381/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree120.table
  base := (41986857458319364338214272930138658346359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-469172425683739204221095120376351000000000000)
      constant := (14955616518557436463644989113958900304774030398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree120.table
  base := (3358948596525767608945033393030727518219/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-8819908596167442236543531890448841000000000000)
      constant := (281447440983645445121386256935479671771407420475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27255092491020445069/5000000000000000000)
  centralHi := (545101849820408901381/100000000000000000000)
  directionLo := (547387402191796871447/100000000000000000000)
  directionHi := (68423425273974608931/12500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree121.table
  base := (86146731116052725092151018002787737605861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-4257728463043588261477947709491819000000000000)
      constant := (136885423502587900625132955118131320768673537989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree121.table
  base := (86146731113075793703487196954066946353391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-80040458320648170758408674590369597750000000000)
      constant := (2576024339351480612043994040230861948021268079119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547387402191796871447/100000000000000000000)
  centralHi := (68423425273974608931/12500000000000000000)
  directionLo := (137415862775858311963/25000000000000000000)
  directionHi := (549663451103433247853/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree122.table
  base := (44172662432668527926685726840359291417587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-4292905094933523684966039335596479000000000000)
      constant := (139189577400507388243073887184428428555904370726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree122.table
  base := (88345324862801237361420742622602313798573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-80701739275789361387925562166699626500000000000)
      constant := (2619384495299059887968909748177047798259406022957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137415862775858311963/25000000000000000000)
  centralHi := (549663451103433247853/100000000000000000000)
  directionLo := (110386022825281411529/20000000000000000000)
  directionHi := (275965057063203528823/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree123.table
  base := (45284748082037918026064988951236995365247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-480897969647051012050458995744571000000000000)
      constant := (15723667817861952308245169504556281669867881934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree123.table
  base := (90569496161915912770513752251978189186563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-9040335581214505779715827749225517250000000000)
      constant := (295900826299469031365050402207757364349280418763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110386022825281411529/20000000000000000000)
  centralHi := (275965057063203528823/50000000000000000000)
  directionLo := (13854687660685486517/2500000000000000000)
  directionHi := (554187506427419460681/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree124.table
  base := (9281924501193234870627206075471371112971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-4363258358713394531942222587805799000000000000)
      constant := (143855722383324020232562530735608923808196943790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree124.table
  base := (92819245010092721679399716990506674319287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-82024301186071742646959337319359684000000000000)
      constant := (2707193163539701608796691899988519642592367193783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13854687660685486517/2500000000000000000)
  centralHi := (554187506427419460681/100000000000000000000)
  directionLo := (556435740837065077717/100000000000000000000)
  directionHi := (278217870418532538859/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree125.table
  base := (95094571408636356622539413623656446199/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-4398434990603329955430314213910459000000000000)
      constant := (146217713468195157224647978359423680063180951000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree125.table
  base := (95094571407069630831516836555155708218743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-82685582141212933276476224895689712750000000000)
      constant := (2751641675832290033186095654969227745054487086487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556435740837065077717/100000000000000000000)
  centralHi := (278217870418532538859/50000000000000000000)
  directionLo := (558674927915640240743/100000000000000000000)
  directionHi := (69834365989455030093/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree126.table
  base := (97395475353973396474267220100564930266293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (64538)
      previous := (32269)
      next := (32269)
      square := (420074004916155109151665316930000000000000)
      linear := (-54735945956706979986646985679199000000000000)
      constant := (1834555353276071508782451946841392848110868997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree126.table
  base := (97395475352639173514506614430296407719393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-9260762566261569322888123608002193500000000000)
      constant := (310716997063646625096633425254332994052771453593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558674927915640240743/100000000000000000000)
  centralHi := (69834365989455030093/12500000000000000000)
  directionLo := (280452588008293384737/50000000000000000000)
  directionHi := (22436207040663470779/4000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree127.table
  base := (311631115149299209620101153579921431571/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-4468788254383200802406497466119779000000000000)
      constant := (150999532824816738507783061454849200094843449280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree127.table
  base := (49860978423319797493480900083491503298467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-84008144051495314535510000048349770250000000000)
      constant := (2841627056761160237526778470571351442837764968806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280452588008293384737/50000000000000000000)
  centralHi := (22436207040663470779/4000000000000000000)
  directionLo := (281563295673837143101/50000000000000000000)
  directionHi := (563126591347674286203/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree128.table
  base := (51037007944957405826507042387528756352149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (5227578)
      previous := (2613789)
      next := (2613789)
      square := (34025994398208563841284890671330000000000000)
      linear := (-4503964886273136225894589092224439000000000000)
      constant := (153419361096554485870348531411390311361866465002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree128.table
  base := (20414803177789477195641662767319363189037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8046090000000000000000000000000000000000000000
      center := (98162298)
      previous := (49081149)
      next := (49081149)
      square := (638932561477471921019682947050530000000000000)
      linear := (-84669425006636505165026887624679799000000000000)
      constant := (2887163925397212491486560784039005279480839357665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell093.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281563295673837143101/50000000000000000000)
  centralHi := (563126591347674286203/100000000000000000000)
  directionLo := (565339278030018818901/100000000000000000000)
  directionHi := (282669639015009409451/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 107
  qDenominator := 207
  table := BinomialMassData.Q107_207.Degree129.table
  base := (204007133750575574644838575689398969527/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 47610000000000000000000000000000000000000000
      center := (580842)
      previous := (290421)
      next := (290421)
      square := (3780666044245395982364987852370000000000000)
      linear := (-504349057573674627709186746481011000000000000)
      constant := (17317607603396769472470467774786449988886040064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q107_207.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 7427
  qDenominator := 14352
  table := BinomialMassData.Q7427_14352.Degree129.table
  base := (52225826239735494099674113834302429715083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 894010000000000000000000000000000000000000000
      center := (10906922)
      previous := (5453461)
      next := (5453461)
      square := (70992506830830213446631438561170000000000000)
      linear := (-9481189551308632866060419466778869750000000000)
      constant := (325895953275655857680641766102937520983228770566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7427_14352.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell093.Kernel129
