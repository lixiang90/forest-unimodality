import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell061.Parameters
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch000_049
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch050_099
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch000_049
import ForestUnimodality.BinomialMassData.Q9287_19012.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree000.table
  base := (104732865741102920523175613/2500000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (546284357262666331322975550000000000000)
      linear := (11965839468518631692750542500000000000)
      constant := (209465731482205841046351226000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree000.table
  base := (104732865741102920523175613/2500000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (42)
      previous := (21)
      next := (21)
      square := (546284357262666331322975550000000000000)
      linear := (11965839468518631692750542500000000000)
      constant := (209465731482205841046351226000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree001.table
  base := (118564346951190829237802668874580904723/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-11754022719245777554796781276181267500000000000)
      constant := (2745569181218338835602882387390092688731245959168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree001.table
  base := (60586043398361987096313505643119527994107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-11786478838621645718206507561045642500000000000)
      constant := (2740212415438032848248863856550976032481246367926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24991763065798337011/50000000000000000000)
  directionHi := (49983526131596674023/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree002.table
  base := (144988222922155575148196815875218251360253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-47556731651234829469664350585469835000000000000)
      constant := (3298334889876383005234047425988535338443737765277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree002.table
  base := (28892021113941155426271037027573454966697/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-47686556128738302123303255724927335000000000000)
      constant := (3286529427030044414433231476761612104068733136365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24991763065798337011/50000000000000000000)
  centralHi := (49983526131596674023/100000000000000000000)
  directionLo := (35343690275267009619/50000000000000000000)
  directionHi := (70687380550534019239/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree003.table
  base := (11232161184942099183587373633989589698439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-35802708931989051914867569309288567500000000000)
      constant := (1040948675093108085360101566275661478384970939804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree003.table
  base := (44705437871317026076181824572841757092007/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-35900077290116656405096748163881692500000000000)
      constant := (1036047636052289261558068812413224848791343965063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35343690275267009619/50000000000000000000)
  centralHi := (70687380550534019239/100000000000000000000)
  directionLo := (43287003400686050253/50000000000000000000)
  directionHi := (86574006801372100507/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree004.table
  base := (58108802462697504948130274090411291221387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-95654104076721378189805926651684435000000000000)
      constant := (1405408570420488359605996711286676383683974709483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree004.table
  base := (5776570006623100806934763909072540982557/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-47956876515864161748541868465299717500000000000)
      constant := (699080674419692863427555003236240007449070150065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43287003400686050253/50000000000000000000)
  centralHi := (86574006801372100507/100000000000000000000)
  directionLo := (19993410452638669609/20000000000000000000)
  directionHi := (49983526131596674023/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree005.table
  base := (39248877728850997985944657519424245087989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-119702790289464652549876714684791735000000000000)
      constant := (1031801119464547685043088768306299783100965290901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree005.table
  base := (38993372185134080530434649965794439758661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-120027351483223334183973977533435485000000000000)
      constant := (1026817079679613136113917694229536180737868478949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19993410452638669609/20000000000000000000)
  centralHi := (49983526131596674023/50000000000000000000)
  directionLo := (111766562185387262013/100000000000000000000)
  directionHi := (55883281092693631007/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree006.table
  base := (27554956539204679194881500105057623966947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-143751476502207926909947502717899035000000000000)
      constant := (831796621347302020686533716879631163555915379523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree006.table
  base := (1710242714925798339500891032948133209739/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-72070474967359172435432109068135767500000000000)
      constant := (414307893702569184320716319461450902245301093208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111766562185387262013/100000000000000000000)
  centralHi := (55883281092693631007/50000000000000000000)
  directionLo := (122434134567480998037/100000000000000000000)
  directionHi := (61217067283740499019/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree007.table
  base := (19907889451810398391216039333053757583541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-3424493116631657168775883484714415000000000000)
      constant := (14998578427619504657192934561718629950073326181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree007.table
  base := (3952185250617038320258256577856265045291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-3433766293596190929750090994675665000000000000)
      constant := (14962386521650001284734336060511343963730039655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122434134567480998037/100000000000000000000)
  centralHi := (61217067283740499019/50000000000000000000)
  directionLo := (132243979794303124287/100000000000000000000)
  directionHi := (2066312184285986317/1562500000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree008.table
  base := (3649848533421025534050916206987365717463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-95924424463847237815044539392056817500000000000)
      constant := (351305231361862529749844278273231373618996180334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree008.table
  base := (7240726924564987873017932413215409483047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-96184073418854183122322349670971817500000000000)
      constant := (350983495519486940941284342782247399570200124423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132243979794303124287/100000000000000000000)
  centralHi := (2066312184285986317/1562500000000000000)
  directionLo := (141374761101068038477/100000000000000000000)
  directionHi := (70687380550534019239/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree009.table
  base := (5344147938479491772299655598738740284983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-107948767570218874995079933408610467500000000000)
      constant := (356787447181209304716202383232041309176713517847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree009.table
  base := (10589105509614270264296321090275610866291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-216481745289203376931534939944779685000000000000)
      constant := (713892608446996828533800446074770652560877777619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141374761101068038477/100000000000000000000)
  centralHi := (70687380550534019239/50000000000000000000)
  directionLo := (37487644598697505517/25000000000000000000)
  directionHi := (149950578394790022069/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree010.table
  base := (765131460605511399178657625185396534781/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-119973110676590512175115327425164117500000000000)
      constant := (378001106486244765111267829930022961429031920145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree010.table
  base := (7564259430086973732580034863051820363061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-240595343740698387618425180547615735000000000000)
      constant := (757195010923967830587643230532228228788294318549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37487644598697505517/25000000000000000000)
  centralHi := (149950578394790022069/100000000000000000000)
  directionLo := (158061788062390575133/100000000000000000000)
  directionHi := (79030894031195287567/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree011.table
  base := (324584219462226651798348585390861831617/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-131997453782962149355150721441717767500000000000)
      constant := (411612874163430766087251087714992286496529052424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree011.table
  base := (2557172674323849857963894221634451135523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-132354471096096699152657710575225892500000000000)
      constant := (412632370525081450494227718604767654062660312707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158061788062390575133/100000000000000000000)
  centralHi := (79030894031195287567/50000000000000000000)
  directionLo := (165776601877430468991/100000000000000000000)
  directionHi := (1295129702167425539/781250000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree012.table
  base := (314433126071642368699061687140794767187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-144021796889333786535186115458271417500000000000)
      constant := (455701799077893202888135878000081729263372108415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree012.table
  base := (1535477172510712810361121957972137273727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-144411270321844204496102830876643917500000000000)
      constant := (457148635695984360924312221356639572400002120543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165776601877430468991/100000000000000000000)
  centralHi := (1295129702167425539/781250000000000000)
  directionLo := (173148013602744201013/100000000000000000000)
  directionHi := (86574006801372100507/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree013.table
  base := (701556968153872167038445068462682461877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-156046139995705423715221509474825067500000000000)
      constant := (509125319287957835560764286459088059410405463893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree013.table
  base := (266794000024806138503348730854974995483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-312936139095183419679095902356123885000000000000)
      constant := (1022030871024808149447359014576433119088657061735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173148013602744201013/100000000000000000000)
  centralHi := (86574006801372100507/50000000000000000000)
  directionLo := (90109083197983013383/50000000000000000000)
  directionHi := (180218166395966026767/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree014.table
  base := (-46568501632870278416064780440278060689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-3430009859226062467250140887579157500000000000)
      constant := (11656606317124397341893017971311001262621882751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree014.table
  base := (-635262534965138417332165951321385163/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-3439283036190596228224348397540407500000000000)
      constant := (11704695914718278124527778492456040907883164625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90109083197983013383/50000000000000000000)
  centralHi := (180218166395966026767/100000000000000000000)
  directionLo := (187021229767297022801/100000000000000000000)
  directionHi := (93510614883648511401/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree015.table
  base := (-1385647204932852783738986471023873521511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-360189652416897396150584595015864735000000000000)
      constant := (1282762610701812375330161661658694646560683305401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree015.table
  base := (-289653080650975039903771284231290247929/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-361163335998173441052876383561795985000000000000)
      constant := (1288462124307596523777853699260806282137118648195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187021229767297022801/100000000000000000000)
  centralHi := (93510614883648511401/50000000000000000000)
  directionLo := (9679268214619857509/5000000000000000000)
  directionHi := (193585364292397150181/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree016.table
  base := (-625799522537910025645071431714824921137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-192119169314820335255327691524486017500000000000)
      constant := (719423006047794214309336312165881589546339485534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree016.table
  base := (-640739848576237011766321510497233621003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-192638467224834225869883312082316017500000000000)
      constant := (722795496021451347938760625981763131585637275946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9679268214619857509/5000000000000000000)
  centralHi := (193585364292397150181/100000000000000000000)
  directionLo := (199934104526386696091/100000000000000000000)
  directionHi := (49983526131596674023/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree017.table
  base := (-1733589201111409139801465879894459152687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-204143512421191972435363085541039667500000000000)
      constant := (805057214983556969894661467487869682981515608817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree017.table
  base := (-881045429084334839691433554531828657349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-204695266450581731213328432383734042500000000000)
      constant := (808982986670130950814787128725379108530741649718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199934104526386696091/100000000000000000000)
  centralHi := (49983526131596674023/25000000000000000000)
  directionLo := (206087357781393589127/100000000000000000000)
  directionHi := (25760919722674198641/12500000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree018.table
  base := (-4294393683020073649514308239003538803049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-432335711055127219230796959115186635000000000000)
      constant := (1796188210168670583991561076753480608868470813559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree018.table
  base := (-4348689425866651719536516905664105354799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-433504131352658473113547105370304135000000000000)
      constant := (1805208509385139245406744957711572562452787597809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206087357781393589127/100000000000000000000)
  centralHi := (25760919722674198641/12500000000000000000)
  directionLo := (42412428330320411543/20000000000000000000)
  directionHi := (53015535412900514429/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree019.table
  base := (-4998650204156190310802425620010421460367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-456384397267870493590867747148293935000000000000)
      constant := (1996755455093997511141387519072528291195055959697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree019.table
  base := (-1262567921364379685920659285027726225487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-228808864902076741900218672986570092500000000000)
      constant := (1003503544540967313073283250212849731930974307234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42412428330320411543/20000000000000000000)
  centralHi := (53015535412900514429/25000000000000000000)
  directionLo := (217873139249454391927/100000000000000000000)
  directionHi := (27234142406181798991/12500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree020.table
  base := (-349479165619354021994525855879757312959/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-240216541740306883975469267590700617500000000000)
      constant := (1105775713920545528799136769406105822001019314952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree020.table
  base := (-705080831745104881695202277190190357841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-240865664127824247243663793287988117500000000000)
      constant := (1111548493699291981706636237797138822157202993724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217873139249454391927/100000000000000000000)
  centralHi := (27234142406181798991/12500000000000000000)
  directionLo := (111766562185387262013/50000000000000000000)
  directionHi := (223533124370774524027/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree021.table
  base := (-6083615034883399863041095030188846778191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-10295546320272592700224680065602215000000000000)
      constant := (49802986374214467053764202153981931392536043169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree021.table
  base := (-1225998755609000295536263008813319421311/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-10323365851166193983147302595485965000000000000)
      constant := (50066290619669115615643724009414532003396776245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111766562185387262013/50000000000000000000)
  centralHi := (223533124370774524027/100000000000000000000)
  directionLo := (45810658399769003547/20000000000000000000)
  directionHi := (28631661499855627217/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree022.table
  base := (-1620863844758057831311286253914014620063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-264265227953050158335540055623807917500000000000)
      constant := (1341468876344405574947421468043248118484050372866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree022.table
  base := (-326364178960656326919383348503073807949/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-264979262579319257930554033890824167500000000000)
      constant := (1348629097422765521078987343025187272019598694590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45810658399769003547/20000000000000000000)
  centralHi := (28631661499855627217/12500000000000000000)
  directionLo := (234443518699187260327/100000000000000000000)
  directionHi := (29305439837398407541/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree023.table
  base := (-6799154123835604940466952806411521100351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-552579142118843591031150899280723135000000000000)
      constant := (2939145718946837707916368299533154261618280655841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree023.table
  base := (-13360338688752916447895703514608635419/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-277036061805066763273999154192242192500000000000)
      constant := (1477473317215798807618210739355082385807542970624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234443518699187260327/100000000000000000000)
  centralHi := (29305439837398407541/12500000000000000000)
  directionLo := (11985628513411820049/5000000000000000000)
  directionHi := (239712570268236400981/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree024.table
  base := (-281513426971823630272541957464197282613/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-576627828331586865391221687313830435000000000000)
      constant := (3208809283613067150223605636124838090267854337075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree024.table
  base := (-3538378815311437759040902265986065471763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-289092861030814268617444274493660217500000000000)
      constant := (1613076193317019524261389350907778296052812821133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11985628513411820049/5000000000000000000)
  centralHi := (239712570268236400981/100000000000000000000)
  directionLo := (122434134567480998037/50000000000000000000)
  directionHi := (9794730765398479843/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree025.table
  base := (-900736789347807076024693045985835677753/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-300338257272165069875646237673468867500000000000)
      constant := (1745891996675871098424112323206702508075443508892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree025.table
  base := (-1448495785269387141755896647667701717293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-602299320513123547921778789590156485000000000000)
      constant := (3510730808424475550740025868248088982476591906815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122434134567480998037/50000000000000000000)
  centralHi := (9794730765398479843/4000000000000000000)
  directionLo := (124958815328991685057/50000000000000000000)
  directionHi := (49983526131596674023/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree026.table
  base := (-3654540829312133693072583244554721143899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-312362600378536707055681631690022517500000000000)
      constant := (1893969956707202006936586151860619036145687395909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree026.table
  base := (-7343415547512371522534842063508590559803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-626412918964618558608669030192992535000000000000)
      constant := (3808551815086957576201351438951200306586175388773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124958815328991685057/50000000000000000000)
  centralHi := (49983526131596674023/20000000000000000000)
  directionLo := (25486697510318632273/10000000000000000000)
  directionHi := (254866975103186322731/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree027.table
  base := (-91907227197561756716742306949396408597/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-324386943484908344235717025706576167500000000000)
      constant := (2048580005878510846202588314723290368802699825080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree027.table
  base := (-3692376435277942143844611599442195964711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-325263258708056784647779635397914292500000000000)
      constant := (2059749131867867608633942098703423959731450116601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25486697510318632273/10000000000000000000)
  centralHi := (254866975103186322731/100000000000000000000)
  directionLo := (259722020404116301519/100000000000000000000)
  directionHi := (3246525255051453769/1250000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree028.table
  base := (-7341053710447446913768762477616864161713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-13731072922093060465949078356046115000000000000)
      constant := (90190587589571114302453598131011113330019676767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree028.table
  base := (-1842791012868188525568182064013051665989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-6884082814975597754922954197945557500000000000)
      constant := (45341475337363884666199033018742564793721530902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259722020404116301519/100000000000000000000)
  centralHi := (3246525255051453769/1250000000000000000)
  directionLo := (10579518383544249943/4000000000000000000)
  directionHi := (2066312184285986317/781250000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree029.table
  base := (-3639359947297843154871563617984339274073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-348435629697651618595787813739683467500000000000)
      constant := (2377190554396442155234984945252200993350363390343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree029.table
  base := (-3653431312254482277787283030560510979969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-349376857159551795334669876000750342500000000000)
      constant := (2390177792537330596390364867023731516406921501279) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10579518383544249943/4000000000000000000)
  centralHi := (2066312184285986317/781250000000000000)
  directionLo := (269169525860362245427/100000000000000000000)
  directionHi := (67292381465090561357/25000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree030.table
  base := (-179234406224616544393994171984887684643/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-360459972804023255775823207756237117500000000000)
      constant := (2551100563730800340412797843462209676544816504260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree030.table
  base := (-7195648800571268474279571917595073371547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-722867312770598601356229992604336735000000000000)
      constant := (5130085419175940352479145137533941051607721379077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269169525860362245427/100000000000000000000)
  centralHi := (67292381465090561357/25000000000000000000)
  directionLo := (68442761914811081053/25000000000000000000)
  directionHi := (273771047659244324213/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree031.table
  base := (-7016451132686517940992105427144906516791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-744968631820789785911717203545581535000000000000)
      constant := (5462721397804479660920145213099958945075015867881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree031.table
  base := (-7040950608842264661774914442678225931659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-746980911222093612043120233207172785000000000000)
      constant := (5492576642727381824172042689580435336373858146069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68442761914811081053/25000000000000000000)
  centralHi := (273771047659244324213/100000000000000000000)
  directionLo := (34787061940510888277/12500000000000000000)
  directionHi := (278296495524087106217/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree032.table
  base := (-6823038342297914794142082185681977017307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-769017318033533060271787991578688835000000000000)
      constant := (5835872027834761935578913059841213906064224407237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree032.table
  base := (-6845860673260788649489432037006366981111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-771094509673588622730010473810008835000000000000)
      constant := (5867759390233749758919393719018634950472418569001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34787061940510888277/12500000000000000000)
  centralHi := (278296495524087106217/100000000000000000000)
  directionLo := (141374761101068038477/50000000000000000000)
  directionHi := (56549904440427215391/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree033.table
  base := (-6591929947872815667149601241565327816793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-793066004246276334631858779611796135000000000000)
      constant := (6221589941872729788684374866469601922702878985863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree033.table
  base := (-6613169207339348144896932270955439595143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-795208108125083633416900714412844885000000000000)
      constant := (6255570627956471173489088071761908830507168130713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141374761101068038477/50000000000000000000)
  centralHi := (56549904440427215391/20000000000000000000)
  directionLo := (287133497157827703509/100000000000000000000)
  directionHi := (28713349715782770351/10000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree034.table
  base := (-395352863849064079115886149030473597089/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-408557345229509804495964783822451717500000000000)
      constant := (3309909106731712974281333889612267470051200217592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree034.table
  base := (-3172696841226244892651094152437087476141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-409660853288289322051895477507840467500000000000)
      constant := (3327976741838533221213426940800930173642711383731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287133497157827703509/100000000000000000000)
  centralHi := (28713349715782770351/10000000000000000000)
  directionLo := (72862884102020804453/25000000000000000000)
  directionHi := (291451536408083217813/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree035.table
  base := (-6026460230223715508823335757912073674137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-17166599523913528231673476646490015000000000000)
      constant := (143479703359700976148956849760312922141202203383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree035.table
  base := (-3022402770678796818922901487245388340687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-8606482704368098518272257098148132500000000000)
      constant := (72131190236854700079790787608276817664021324833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72862884102020804453/25000000000000000000)
  centralHi := (291451536408083217813/100000000000000000000)
  directionLo := (295706528435170441763/100000000000000000000)
  directionHi := (73926632108792610441/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree036.table
  base := (-1424106451086403684567220273301635936517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-432606031442253078856035571855559017500000000000)
      constant := (3726802662181557355951783207598199370686842048694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree036.table
  base := (-714181783894963224570825198714771088169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-433774451739784332738785718110676517500000000000)
      constant := (3747116903289459094705586017432020764156937309916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295706528435170441763/100000000000000000000)
  centralHi := (73926632108792610441/25000000000000000000)
  directionLo := (299901156789580044137/100000000000000000000)
  directionHi := (149950578394790022069/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree037.table
  base := (-1334348788581435679451235360957772240711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-444630374548624716036070965872112667500000000000)
      constant := (3944537970169535512760862746627935491130295265202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree037.table
  base := (-2676594553822716644324052593823653023561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-445831250965531838082230838412094542500000000000)
      constant := (3966021598838120412885656130479994720131856236951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299901156789580044137/100000000000000000000)
  centralHi := (149950578394790022069/50000000000000000000)
  directionLo := (304037919885458169437/100000000000000000000)
  directionHi := (152018959942729084719/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree038.table
  base := (-495104037059442154402006556314497793303/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-456654717654996353216106359888666317500000000000)
      constant := (4168439769171628275898216049124835945105058936365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree038.table
  base := (-496567861001588500836514780563067433573/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-457888050191279343425675958713512567500000000000)
      constant := (4191123561033899616529687519843817763952727274215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304037919885458169437/100000000000000000000)
  centralHi := (152018959942729084719/50000000000000000000)
  directionLo := (61623829680676058337/20000000000000000000)
  directionHi := (154059574201690145843/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree039.table
  base := (-2269435309301069979283281275631048109873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-468679060761367990396141753905219967500000000000)
      constant := (4398491012402698405255310120213173387720426068143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree039.table
  base := (-2276214159119365276877081760871201629307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-469944849417026848769121079014930592500000000000)
      constant := (4422405784043316963838546453230650212401510899237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61623829680676058337/20000000000000000000)
  centralHi := (154059574201690145843/50000000000000000000)
  directionLo := (312147020644715260949/100000000000000000000)
  directionHi := (6242940412894305219/2000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree040.table
  base := (-820449603310792880935436933531306072119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-961406807735479255152354295843547235000000000000)
      constant := (9269352628100862081799620824397346213715025109645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree040.table
  base := (-1028699170654206687971052124235091760953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-482001648642774354112566199316348617500000000000)
      constant := (4659852923484863509159218684963639672824969856846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312147020644715260949/100000000000000000000)
  centralHi := (6242940412894305219/2000000000000000000)
  directionLo := (316123576124781150267/100000000000000000000)
  directionHi := (79030894031195287567/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree041.table
  base := (-3642401964545619500116430769747675359731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-985455493948222529512425083876654535000000000000)
      constant := (9753963574841025249961994496594218935719238741421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree041.table
  base := (-913502358903761011758201911678847262497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-494058447868521859456011319617766642500000000000)
      constant := (4903451134091966512296450433110997430266609821054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316123576124781150267/100000000000000000000)
  centralHi := (79030894031195287567/25000000000000000000)
  directionLo := (20003170477849051161/6250000000000000000)
  directionHi := (320050727645584818577/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree042.table
  base := (-632088415341363198857302879723704208343/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-20602126125733995997397874936933915000000000000)
      constant := (209199791790267254944706104210008923440406674685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree042.table
  base := (-3171172558809821299224413967761026947073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-20657765187521198563243119996701415000000000000)
      constant := (210334200948765403714810637499531955875294517007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20003170477849051161/6250000000000000000)
  centralHi := (320050727645584818577/100000000000000000000)
  directionLo := (161965136025485680787/50000000000000000000)
  directionHi := (12957210882038854463/4000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree043.table
  base := (-1328684926429658058591941145326009494033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-516776433186854539116283329971434567500000000000)
      constant := (5379904335927792939925862427648176632836215050703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree043.table
  base := (-33341049782287139155574989351074641513/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-518172046320016870142901560220602692500000000000)
      constant := (5409052018816102694096047595202971378306321735320) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161965136025485680787/50000000000000000000)
  centralHi := (12957210882038854463/4000000000000000000)
  directionLo := (163881949917893890683/50000000000000000000)
  directionHi := (327763899835787781367/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree044.table
  base := (-2134089212717896221536977290479359861591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1057601552586452352592637447975976435000000000000)
      constant := (11280999776780084622627896316752918157052558964681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree044.table
  base := (-535811035641851945760193429963810386643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-530228845545764375486346680522020717500000000000)
      constant := (5671033249931273878441282564393795437262109014426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163881949917893890683/50000000000000000000)
  centralHi := (327763899835787781367/100000000000000000000)
  directionLo := (165776601877430468991/50000000000000000000)
  directionHi := (331553203754860937983/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree045.table
  base := (-99463500223583466386699803236092435759/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-540825119399597813476354118004541867500000000000)
      constant := (5907172340841506369539539543605769597021492073352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree045.table
  base := (-1599865504645198728020103348055446213191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1084571289543023761659583601646877485000000000000)
      constant := (11878244878756477908785359997782006732098786200281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165776601877430468991/50000000000000000000)
  centralHi := (331553203754860937983/100000000000000000000)
  directionLo := (335299686556161786039/100000000000000000000)
  directionHi := (8382492163904044651/2500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree046.table
  base := (-4120346326261582909074889944831008017/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-552849462505969450656389512021095517500000000000)
      constant := (6179913375768230377620288439467320316801110105875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree046.table
  base := (-518940579662775008384844403768395708611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-554342443997259386173236921124856767500000000000)
      constant := (6213311306529852277727976493356621174881207521501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335299686556161786039/100000000000000000000)
  centralHi := (8382492163904044651/2500000000000000000)
  directionLo := (339004767944653469191/100000000000000000000)
  directionHi := (42375595993081683649/12500000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree047.table
  base := (-225382778380677889160756881330550706393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-564873805612341087836424906037649167500000000000)
      constant := (6458715486064073096948465805720885763266919379463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree047.table
  base := (-457952576452445152771506341982049945039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1132798486446013783033364082852549585000000000000)
      constant := (12987184759501029036971331238922474014353174445649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339004767944653469191/100000000000000000000)
  centralHi := (42375595993081683649/12500000000000000000)
  directionLo := (85667447717086635777/25000000000000000000)
  directionHi := (342669790868346543109/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree048.table
  base := (18243402041809210523677322295753067999/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-576898148718712725016460300054202817500000000000)
      constant := (6743571896069826922755570961454639972883772083964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree048.table
  base := (69661698854340707315537833840459087731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-578456042448754396860127161727692817500000000000)
      constant := (6779958917360548653648734337612922505815062810579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85667447717086635777/25000000000000000000)
  centralHi := (342669790868346543109/100000000000000000000)
  directionLo := (173148013602744201013/50000000000000000000)
  directionHi := (346296027205488402027/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree049.table
  base := (1483418612193116855182732025569876567/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (5139989517484427511417876949950000000000000)
      linear := (-245282170689331262889002788034467500000000000)
      constant := (2929811116328961942556112531979407013966439168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree049.table
  base := (150681645395965414899198469431484980247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (790356)
      previous := (395178)
      next := (395178)
      square := (10279979034968855022835753899900000000000000)
      linear := (-491889080945024491631463791777685000000000000)
      constant := (5891216023591947223593731615814069210895720115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173148013602744201013/50000000000000000000)
  centralHi := (346296027205488402027/100000000000000000000)
  directionLo := (4373558536514708977/1250000000000000000)
  directionHi := (349884682921176718161/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree050.table
  base := (694717562945885269369083346403264096831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-600946834931455999376531088087310117500000000000)
      constant := (7331423749148466764894370682570188069340885992479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree050.table
  base := (1383815988585782447530353112781931827393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1205139281800498815094034804661057735000000000000)
      constant := (14741849295784744906560083937142076074450021709537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4373558536514708977/1250000000000000000)
  centralHi := (349884682921176718161/100000000000000000000)
  directionLo := (353436902752670096193/100000000000000000000)
  directionHi := (176718451376335048097/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree051.table
  base := (254410070105920687636683538804076050437/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-612971178037827636556566482103863767500000000000)
      constant := (7634408690773809542420160475733972836418426883732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree051.table
  base := (1015054116507117214651850468250611109219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-614626440125996912890462522631946892500000000000)
      constant := (7675513399562828732239532631674234618573866411971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353436902752670096193/100000000000000000000)
  centralHi := (176718451376335048097/50000000000000000000)
  directionLo := (178476887237499456979/50000000000000000000)
  directionHi := (356953774474998913959/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree052.table
  base := (2696648562329051353679003094284747457517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1249991042288398547473203752240834835000000000000)
      constant := (15886853637516035319358741623970190148375493664653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree052.table
  base := (2691889346047418859281449801313305715197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1253366478703488836467815285866729835000000000000)
      constant := (15972333245342648919494979310667393546231766863773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178476887237499456979/50000000000000000000)
  centralHi := (356953774474998913959/100000000000000000000)
  directionLo := (90109083197983013383/25000000000000000000)
  directionHi := (360436332791932053533/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree053.table
  base := (421647480526840060878898288892159284973/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-637019864250570910916637270136971067500000000000)
      constant := (8258474074783082062619821527383272915495034431028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree053.table
  base := (3368802363904795076601795985726233683831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1277480077154983847154705526469565885000000000000)
      constant := (16605760570263740403513431123470390896687529275479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90109083197983013383/25000000000000000000)
  centralHi := (360436332791932053533/100000000000000000000)
  directionLo := (363885562891748154247/100000000000000000000)
  directionHi := (45485695361468519281/12500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree054.table
  base := (4064550127197607743621760826116905021991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1298088414713885096193345328307049435000000000000)
      constant := (17159093591901267857048417969168776151403943878919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree054.table
  base := (1015131299307383961865343742462225658837/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-650796837803239428920797883536200967500000000000)
      constant := (8625650748782686514142061894829160345287635193066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363885562891748154247/100000000000000000000)
  centralHi := (45485695361468519281/12500000000000000000)
  directionLo := (5739100057850671783/1562500000000000000)
  directionHi := (367302403702442994113/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree055.table
  base := (4770466727946750326057573022916890417713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1322137100926628370553416116340156735000000000000)
      constant := (17813283352509582584250492457292512790178568142417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree055.table
  base := (953353444795298417189057665421601045239/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1325707274057973868528486007675237985000000000000)
      constant := (17908949461802309232400812065642379502537018280755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5739100057850671783/1562500000000000000)
  centralHi := (367302403702442994113/100000000000000000000)
  directionLo := (370687750876853788279/100000000000000000000)
  directionHi := (9267193771921344707/2500000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree056.table
  base := (2745332740297991928267823721363404179277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-13736589664687465764423335758910857500000000000)
      constant := (188566443506302533618280001023683575226218047357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree056.table
  base := (685908276895193710236408356933229381307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-13773682372545600808320165798755857500000000000)
      constant := (189578556519971518705548909555295007028748642348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370687750876853788279/100000000000000000000)
  centralHi := (9267193771921344707/2500000000000000000)
  directionLo := (374042459534594045603/100000000000000000000)
  directionHi := (93510614883648511401/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree057.table
  base := (77811349477272791483210004647976612073/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-685117236676057459636778846203185667500000000000)
      constant := (9578886269459893527697210895692583037755226066280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree057.table
  base := (6221785560953276126699996459958076420403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1373934470960963889902266488880910085000000000000)
      constant := (19260543383775240450228407319874748539036011956627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374042459534594045603/100000000000000000000)
  centralHi := (93510614883648511401/25000000000000000000)
  directionLo := (94341836696145983909/25000000000000000000)
  directionHi := (377367346784583935637/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree058.table
  base := (108952796325084635728406901864302325047/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-697141579782429096816814240219739317500000000000)
      constant := (9924030858461755568727426974556902561823446477536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree058.table
  base := (1742527941941182436581579416255425325251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-699024034706229450294578364741873067500000000000)
      constant := (9977239586610430021006912675945506703393146536518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94341836696145983909/25000000000000000000)
  centralHi := (377367346784583935637/100000000000000000000)
  directionLo := (190331597024629911551/50000000000000000000)
  directionHi := (380663194049259823103/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree059.table
  base := (241708883504412608689079561679541617851/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-709165922888800733996849634236292967500000000000)
      constant := (10275187304907484874492749047529571878125944026544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree059.table
  base := (7732052199869894052698229148937209499257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1422161667863953911276046970086582185000000000000)
      constant := (20660501555458647448483864257960728167732600380313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190331597024629911551/50000000000000000000)
  centralHi := (380663194049259823103/100000000000000000000)
  directionLo := (191965374604596627221/50000000000000000000)
  directionHi := (383930749209193254443/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree060.table
  base := (8509848576484917277552288458771042370253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1442380531990344742353770056505693235000000000000)
      constant := (21264707257306602074057609351139378097125766855277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree060.table
  base := (4253716520827866693688932907638459322381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-723137633157724460981468605344709117500000000000)
      constant := (10689303301909262120280716650874854590798043072429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191965374604596627221/50000000000000000000)
  centralHi := (383930749209193254443/100000000000000000000)
  directionLo := (9679268214619857509/2500000000000000000)
  directionHi := (387170728584794300361/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree061.table
  base := (9298313654853175237635544679949466534493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1466429218203088016713840844538800535000000000000)
      constant := (21991056084981566503913146905911025565525930173437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree061.table
  base := (4648048729477353408527355201141973015861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-735194432383471966324913725646127142500000000000)
      constant := (11054395387629199996757123094001475677679072993749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9679268214619857509/2500000000000000000)
  centralHi := (387170728584794300361/100000000000000000000)
  directionLo := (390383818769974714119/100000000000000000000)
  directionHi := (9759595469249367853/2500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree062.table
  base := (157811510949070274227137359572947324357/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-745238952207915645536955816285953917500000000000)
      constant := (11364708933348406242832803363649382200654396998816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree062.table
  base := (10097903940008413394696432218303361388351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1494502463218438943336717691895090335000000000000)
      constant := (22851050872884867065722287010774301934354489936159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390383818769974714119/100000000000000000000)
  centralHi := (9759595469249367853/2500000000000000000)
  directionLo := (393570678331067327859/100000000000000000000)
  directionHi := (19678533916553366393/5000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree063.table
  base := (10914588822029216592912216401638841943519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-30908705931195399294571069808265615000000000000)
      constant := (479179381441823464509735105503229505828481943279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree063.table
  base := (1364090599814143611491208276431606122063/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-15496082261938101571669468698958432500000000000)
      constant := (240871265429953972430908520661391857722488190332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393570678331067327859/100000000000000000000)
  centralHi := (19678533916553366393/5000000000000000000)
  directionLo := (198365969691454686431/50000000000000000000)
  directionHi := (396731939382909372863/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree064.table
  base := (11742153685253243574708123828171080416303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1538575276841317839794053208638122435000000000000)
      constant := (24242168928748798916796485053156992771224424819727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree064.table
  base := (5870222411456315390895056187632707462703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-771364830060714482355249086550381217500000000000)
      constant := (12185893795132480904230648493002227902984290637327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198365969691454686431/50000000000000000000)
  centralHi := (396731939382909372863/100000000000000000000)
  directionLo := (399868209052773392183/100000000000000000000)
  directionHi := (49983526131596674023/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree065.table
  base := (12582526291955998117301492475346891763309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1562623963054061114154123996671229735000000000000)
      constant := (25016553208974082359681305306912813247446939488781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree065.table
  base := (2516192011530025940084812298445402638301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1566843258572923975397388413703598485000000000000)
      constant := (25150259258812366923349689474722220410052408178545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399868209052773392183/100000000000000000000)
  centralHi := (49983526131596674023/12500000000000000000)
  directionLo := (201490035420874158551/50000000000000000000)
  directionHi := (402980070841748317103/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree066.table
  base := (6717805937136081728171790824712897295769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-793336324633402194257097392352168517500000000000)
      constant := (12901470195211750903910113825387374877724793140921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree066.table
  base := (13434176703488095151934304779175676497753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1590956857024418986084278654306434535000000000000)
      constant := (25940796898758284946503444184274404817841826502777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201490035420874158551/50000000000000000000)
  centralHi := (402980070841748317103/100000000000000000000)
  directionLo := (25379255368263529931/6250000000000000000)
  directionHi := (406068085892216478897/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree067.table
  base := (14301324898116919652268299816653567960251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1610721335479547662874265572737444335000000000000)
      constant := (26601328540795777287195135054808936886172141983259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree067.table
  base := (7150005062631422760851226158553164700813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-807535227737956998385584447454635292500000000000)
      constant := (13371699299054485715046791268217628049484548790317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25379255368263529931/6250000000000000000)
  centralHi := (406068085892216478897/100000000000000000000)
  directionLo := (409132794169223872239/100000000000000000000)
  directionHi := (5114159927115298403/1250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree068.table
  base := (15179588163498118292817954990046421594401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1634770021692290937234336360770551635000000000000)
      constant := (27411715916065191373095378289018195950656907340609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree068.table
  base := (7589191978289164891941686360502426409267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-819592026963704503729029567756053317500000000000)
      constant := (13779031315835242943915388967739868912033588480403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409132794169223872239/100000000000000000000)
  centralHi := (5114159927115298403/1250000000000000000)
  directionLo := (82434943112557435651/20000000000000000000)
  directionHi := (25760919722674198641/6250000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree069.table
  base := (16070331992488398671218807639850937394807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1658818707905034211594407148803658935000000000000)
      constant := (28234100942137059958447985442722211712844521490263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree069.table
  base := (8034614645984190692482186634840923099219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-831648826189452009072474688057471342500000000000)
      constant := (14192393721399411000954563079264612877302764321971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82434943112557435651/20000000000000000000)
  centralHi := (25760919722674198641/6250000000000000000)
  directionLo := (415194350917510102983/100000000000000000000)
  directionHi := (51899293864688762873/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree070.table
  base := (16973493496316251497550384640408733870433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-34344232533015867060295468098709515000000000000)
      constant := (593234330577358773019199581597040358072358300753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree070.table
  base := (16972483957982120069302917522454276567819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (38727444)
      previous := (19363722)
      next := (19363722)
      square := (503718972713473896118951941095100000000000000)
      linear := (-34436964302661204670037543198322015000000000000)
      constant := (596399420957816150518683354368763704623103839579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415194350917510102983/100000000000000000000)
  centralHi := (51899293864688762873/12500000000000000000)
  directionLo := (418192182995283318181/100000000000000000000)
  directionHi := (209096091497641659091/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree071.table
  base := (178890159138672092208400969236171631413/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-853458040165260380157274362434936767500000000000)
      constant := (14957429201117451672549765368612842458789788285850) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree071.table
  base := (111800574096762510489349585001493758803/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-855762424640947019759364928660307392500000000000)
      constant := (15037206958368436428012476563926155477734992178160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418192182995283318181/100000000000000000000)
  centralHi := (209096091497641659091/50000000000000000000)
  directionLo := (26323042336019244323/6250000000000000000)
  directionHi := (421168677376307909169/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree072.table
  base := (9408424007318717280859642885087780288781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-865482383271632017337309756451490417500000000000)
      constant := (15386614198310628548705743138094342020293874170029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree072.table
  base := (18816002366197299894843277663306301372991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1735638447733389050205620097923450835000000000000)
      constant := (30937313168692656901071386246493265394073952037919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26323042336019244323/6250000000000000000)
  centralHi := (421168677376307909169/100000000000000000000)
  directionLo := (424124283303204115431/100000000000000000000)
  directionHi := (53015535412900514429/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree073.table
  base := (9878471779929945336755197623765589574921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-877506726378003654517345150468044067500000000000)
      constant := (15821795568434619428285010914486836206727346485289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree073.table
  base := (1234760613578468469593984369470352942947/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-879876023092442030446255169263143442500000000000)
      constant := (15906134175502034686665994363168368926038337308184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424124283303204115431/100000000000000000000)
  centralHi := (53015535412900514429/12500000000000000000)
  directionLo := (106764858618134668277/25000000000000000000)
  directionHi := (427059434472538673109/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree074.table
  base := (828370432645405503099188256617830645063/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1779062138968750583394761088969195435000000000000)
      constant := (32525945680179246273420604142398257206577350964175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree074.table
  base := (5177138249506834417218042844714548255447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-891932822318189535789700289564561467500000000000)
      constant := (16349639266340706985421567190357167037889474952046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106764858618134668277/25000000000000000000)
  centralHi := (427059434472538673109/100000000000000000000)
  directionLo := (429974549777719472359/100000000000000000000)
  directionHi := (10749363744442986809/2500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree075.table
  base := (10836881058225522789631345910980383301869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-901555412590746928877415938501151367500000000000)
      constant := (16710145587807734661464338463757247819245972295821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree075.table
  base := (10836557362087357375081688134578148488263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-903989621543937041133145409865979492500000000000)
      constant := (16799171436846486877581285516029395257451685827367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429974549777719472359/100000000000000000000)
  centralHi := (10749363744442986809/2500000000000000000)
  directionLo := (108217508501715125633/25000000000000000000)
  directionHi := (432870034006860502533/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree076.table
  base := (22650413463974155684033599987562570052539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1827159511394237132114902665035410035000000000000)
      constant := (34326626855155137361441000679216932418120039021851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree076.table
  base := (905992857771591356407571072416175485001/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1832092841539369092953181060334795035000000000000)
      constant := (34509460616078592185858886964819713438180923900225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108217508501715125633/25000000000000000000)
  centralHi := (432870034006860502533/100000000000000000000)
  directionLo := (87149255699781756771/20000000000000000000)
  directionHi := (27234142406181798991/6250000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree077.table
  base := (1181959208722264604238082114821157365043/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-18889879567418167413009933194576707500000000000)
      constant := (359642367608264032550697557026615295877367897630) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree077.table
  base := (11819321442482169368946750202255172656369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-18940882040723103098368074499363582500000000000)
      constant := (361557459958484000114551530266594392056665020129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87149255699781756771/20000000000000000000)
  centralHi := (27234142406181798991/6250000000000000000)
  directionLo := (438603661761044333251/100000000000000000000)
  directionHi := (109650915440261083313/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree078.table
  base := (12320023276709037157940224231841336405949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-937628441909861840417522120550812317500000000000)
      constant := (18087633030667097688697861297242997244818821512541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree078.table
  base := (2463955173053491042089648090761816415899/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-940160019221179557163480770770233567500000000000)
      constant := (18183926818081546983176186972903227553789610260455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438603661761044333251/100000000000000000000)
  centralHi := (109650915440261083313/25000000000000000000)
  directionLo := (441442550050110813563/100000000000000000000)
  directionHi := (110360637512527703391/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree079.table
  base := (12826487802472728671118695414106566535181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-949652785016233477597557514567365967500000000000)
      constant := (18558784198822216632905274184491913497805372787629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree079.table
  base := (1282626166705794931029350084779208868131/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-952216818446927062506925891071651592500000000000)
      constant := (18657563869987781816008944930801674156778272341790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441442550050110813563/100000000000000000000)
  centralHi := (110360637512527703391/25000000000000000000)
  directionLo := (444263297920605408881/100000000000000000000)
  directionHi := (222131648960302704441/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree080.table
  base := (2667794876865020128872435186526254466921/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-961677128122605114777592908583919617500000000000)
      constant := (19035929262439451792899555776563533366992512566445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree080.table
  base := (26677535456863994269760447847222028942611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1928547235345349135700742022746139235000000000000)
      constant := (38274452884970931663495596652990874780840785584499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444263297920605408881/100000000000000000000)
  centralHi := (222131648960302704441/50000000000000000000)
  directionLo := (111766562185387262013/25000000000000000000)
  directionHi := (447066248741549048053/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree081.table
  base := (27714945682413717748696550380099789570509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1947402942457953503915256605200946535000000000000)
      constant := (39038135983036802047599604235142512264585474953581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree081.table
  base := (13857284016357894242108391134610146086199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-976330416898422073193816131674487642500000000000)
      constant := (19622914308918289498055925662096851114224636384791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111766562185387262013/25000000000000000000)
  centralHi := (447066248741549048053/100000000000000000000)
  directionLo := (224925867592185033103/50000000000000000000)
  directionHi := (449851735184370066207/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree082.table
  base := (28763947968187196709923953637527086342441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1971451628670696778275327393234053835000000000000)
      constant := (40016400356939462581786447635439015890305861712969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree082.table
  base := (7190900739027479659574577793255541250567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-988387216124169578537261251975905667500000000000)
      constant := (20114627264774802968369078641957649922132860704206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224925867592185033103/50000000000000000000)
  centralHi := (449851735184370066207/100000000000000000000)
  directionLo := (226310039841881860851/50000000000000000000)
  directionHi := (452620079683763721703/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree083.table
  base := (29824939038672121233609382170631196206673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-1995500314883440052635398181267161135000000000000)
      constant := (41006651271863075106508622223504925431685715603057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree083.table
  base := (29824623890448234666995957037010879747647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2000888030699834167761412744554647385000000000000)
      constant := (41224730251049776647872543876783125534977011105823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226310039841881860851/50000000000000000000)
  centralHi := (452620079683763721703/100000000000000000000)
  directionLo := (455371594873334878839/100000000000000000000)
  directionHi := (11384289871833371971/2500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree084.table
  base := (308979039228367841088276861047604793531/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-20607642868328401295872132339798657500000000000)
      constant := (428662126424458444743660745308118743080716288550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree084.table
  base := (15448808047634923821767867202513738643373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-20663281930115603861717377399566157500000000000)
      constant := (430941382136073535955329180167257379077879331293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455371594873334878839/100000000000000000000)
  centralHi := (11384289871833371971/2500000000000000000)
  directionLo := (458106583997690035471/100000000000000000000)
  directionHi := (28631661499855627217/6250000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree085.table
  base := (15991414554216770272574872330630681032801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1021798843654463300677769878666687867500000000000)
      constant := (21511555702442855931603726352069250084638136686209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree085.table
  base := (15991283135154934603523355987510900276129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1024557613801412094567596612880159742500000000000)
      constant := (21625914911969745884321437082928297935736132724161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458106583997690035471/100000000000000000000)
  centralHi := (28631661499855627217/6250000000000000000)
  directionLo := (23041267065125815453/5000000000000000000)
  directionHi := (460825341302516309061/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree086.table
  base := (33079702399860347376230627445086860729261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2067646373521669875715610545366483035000000000000)
      constant := (44049320042218472423905434395674635511516481814349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree086.table
  base := (206746640092457864612568357531325780873/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1036614413027159599911041733181577767500000000000)
      constant := (22141726551876507712143544081820880841060717668560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23041267065125815453/5000000000000000000)
  centralHi := (460825341302516309061/100000000000000000000)
  directionLo := (231764076202033870783/50000000000000000000)
  directionHi := (463528152404067741567/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree087.table
  base := (17094256394935766506077595836183201761901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1045847529867206575037840666699795167500000000000)
      constant := (22543757026465211617436940407468668852901921348109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree087.table
  base := (34188293700475350597983235014575627339457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2097342424505814210508973706965991585000000000000)
      constant := (45327125044154804822024006753498312860906319142113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231764076202033870783/50000000000000000000)
  centralHi := (463528152404067741567/100000000000000000000)
  directionLo := (116553823659843056969/25000000000000000000)
  directionHi := (466215294639372227877/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree088.table
  base := (17654625171894205517333415302999369528121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1057871872973578212217876060716348817500000000000)
      constant := (23068846606293574339564889597409645874004107264089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree088.table
  base := (1412362014283442359497430623465290248907/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2121456022957309221195863947568827635000000000000)
      constant := (46382845424424600494016513510368035610016756929075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116553823659843056969/25000000000000000000)
  centralHi := (466215294639372227877/100000000000000000000)
  directionLo := (234443518699187260327/50000000000000000000)
  directionHi := (93777407479674904131/20000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree089.table
  base := (364419060949918260185372955459419089783/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1069896216079949849397911454732902467500000000000)
      constant := (23599928659311837358444699670941805728352978052350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree089.table
  base := (1138803861530185725344873446433969101281/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1072784810704402115941377094085831842500000000000)
      constant := (23725307022703880341808893746153886429464175720464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234443518699187260327/50000000000000000000)
  centralHi := (93777407479674904131/20000000000000000000)
  directionLo := (58942955304892653731/12500000000000000000)
  directionHi := (471543642439141229849/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree090.table
  base := (37586471950597385745597798805112262241391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2163841118372642973155893697498912235000000000000)
      constant := (48274006188213577207592560209972300887305624253519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree090.table
  base := (4698288172725091659965615988976837963131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1084841609930149621284822214387249867500000000000)
      constant := (24265215363704150064338285032203354632616536356716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58942955304892653731/12500000000000000000)
  centralHi := (471543642439141229849/100000000000000000000)
  directionLo := (474185364187171725401/100000000000000000000)
  directionHi := (237092682093585862701/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree091.table
  base := (19371470303160618790573692700945449076287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-22325406169238635178734331485020607500000000000)
      constant := (503674894452507284671572028701908292037580434767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree091.table
  base := (3874278861846771633803690998402414012177/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2305205000000000000000000000000000000000000000
      center := (19363722)
      previous := (9681861)
      next := (9681861)
      square := (251859486356736948059475970547550000000000000)
      linear := (-22385681819508104625066680299768732500000000000)
      constant := (506349952125385459479292019386859500542940481285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474185364187171725401/100000000000000000000)
  centralHi := (237092682093585862701/50000000000000000000)
  directionLo := (95362490003956731643/20000000000000000000)
  directionHi := (59601556252472957277/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree092.table
  base := (39911305469640914923390493921286693772187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2211938490798129521876035273565126835000000000000)
      constant := (50458257574088350411850532206241629460587720466683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree092.table
  base := (39911166803103782352139165367244502308747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2217910416763289263943424909980171835000000000000)
      constant := (50726207641749903582957625465252854951857424255723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95362490003956731643/20000000000000000000)
  centralHi := (59601556252472957277/12500000000000000000)
  directionLo := (11985628513411820049/2500000000000000000)
  directionHi := (479425140536472801961/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree093.table
  base := (1643662423617721162941745223885335126607/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2235987177010872796236106061598234135000000000000)
      constant := (51568359807022421634587264193613245287829871911575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree093.table
  base := (41091434092591894405102779273270829829131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2242024015214784274630315150583007885000000000000)
      constant := (51842167595792776221593919394088009606107366883179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11985628513411820049/2500000000000000000)
  centralHi := (479425140536472801961/100000000000000000000)
  directionLo := (60252958727010439679/12500000000000000000)
  directionHi := (482023669816083517433/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree094.table
  base := (10570925149607082575049352955658604196109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1130017931611808035298088424815670717500000000000)
      constant := (26345223116913724441324368903578133564143472367962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree094.table
  base := (10570896303685305697218351254937019070631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1133068806833139642658602695592921967500000000000)
      constant := (26485087525656141230613688284013746010765593113358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60252958727010439679/12500000000000000000)
  centralHi := (482023669816083517433/100000000000000000000)
  directionLo := (242304132830783920063/50000000000000000000)
  directionHi := (484608265661567840127/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree095.table
  base := (21743860323307868783038263218062325992433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1142042274718179672478123818832224367500000000000)
      constant := (26912258372502619465746068578469858475305987834897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree095.table
  base := (543595192656337361854650697795827733229/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1145125606058887148002047815894339992500000000000)
      constant := (27055114950420990448058600300472720860603037522440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242304132830783920063/50000000000000000000)
  centralHi := (484608265661567840127/100000000000000000000)
  directionLo := (60897393729132191329/12500000000000000000)
  directionHi := (487179149833057530633/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree096.table
  base := (174623501407621433307153020738745331959/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 112955045000000000000000000000000000000000000000
      center := (948822378)
      previous := (474411189)
      next := (474411189)
      square := (12341114831480110454914322556829950000000000000)
      linear := (-1154066617824551309658159212848778017500000000000)
      constant := (27485285620863970095779331092360886832703200848768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree096.table
  base := (44703520393659954616863108963000700095187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (1897644756)
      previous := (948822378)
      next := (948822378)
      square := (24682229662960220909828645113659900000000000000)
      linear := (-2314364810569269306690985872391516035000000000000)
      constant := (55262332047416082174516422639307997442856670373683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60897393729132191329/12500000000000000000)
  centralHi := (487179149833057530633/100000000000000000000)
  directionLo := (489736538269923992149/100000000000000000000)
  directionHi := (9794730765398479843/2000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree097.table
  base := (45931383791284248737448873122802428115057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2623257483575323723012928591100000000000000)
      linear := (-247867140170246136005567989555815000000000000)
      constant := (5965417114974847417249465806196066129904251857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree097.table
  base := (45931296285373139004322636713722161922317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (201684)
      previous := (100842)
      next := (100842)
      square := (2623257483575323723012928591100000000000000)
      linear := (-248536338507892902261438634604565000000000000)
      constant := (5997075289992934118179911257486051910775483117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell061.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489736538269923992149/100000000000000000000)
  centralHi := (9794730765398479843/2000000000000000000)
  directionLo := (492280641302455376699/100000000000000000000)
  directionHi := (4922806413024553767/1000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree098.table
  base := (5896377421978815314882810339525166197223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (5139989517484427511417876949950000000000000)
      linear := (-490676927962221817583602665923317500000000000)
      constant := (11932243199440121275036000701357121654998684828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9287
  qDenominator := 19012
  table := BinomialMassData.Q9287_19012.Degree098.table
  base := (2948183724577835153642704091708233791929/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 47045000000000000000000000000000000000000000
      center := (395178)
      previous := (197589)
      next := (197589)
      square := (5139989517484427511417876949950000000000000)
      linear := (-492001667528583783437060881632067500000000000)
      constant := (11995559743915501296812324123007970923986079688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9287_19012.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell061.Kernel098
