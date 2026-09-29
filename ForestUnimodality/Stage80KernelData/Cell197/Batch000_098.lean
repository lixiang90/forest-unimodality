import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell197.Parameters
import ForestUnimodality.BinomialMassData.Q97_177.Batch000_049
import ForestUnimodality.BinomialMassData.Q97_177.Batch050_099
import ForestUnimodality.BinomialMassData.Q49_89.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_89.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree000.table
  base := (547834496061607437522411611/20000000000000000000000000)
  polynomial :=
    { denominator := 885000000000000000000000000000000000000000
      center := (3007)
      previous := (0)
      next := (2480)
      square := (121308927980230751159096412150000000000000)
      linear := (-437023471293643810675622066250000000000000)
      constant := (24241676450726129110366713786750000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree000.table
  base := (547834496061607437522411611/20000000000000000000000000)
  polynomial :=
    { denominator := 445000000000000000000000000000000000000000
      center := (1519)
      previous := (0)
      next := (1240)
      square := (60997144577630151712765992550000000000000)
      linear := (-219746265226747452825595276250000000000000)
      constant := (12189317537370765484873658344750000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree001.table
  base := (21387030629925480312461916496716877644689/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-100887086447139720214449809683350000000000000)
      constant := (2728976970431077997746905174015372238921846724) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree001.table
  base := (170625904428471996411129017514013063435173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-51070275547576556338658093712300000000000000)
      constant := (1376354027332639843932884906106897475470005333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49743693530738551289/100000000000000000000)
  directionHi := (4974369353073855129/10000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree002.table
  base := (109076468952796857199197485008738413695177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-248842036950608971878629027280900000000000000)
      constant := (3638410309050930995934937816636165762656200233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree002.table
  base := (4340570880772276661341114825262583142433/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-63025715884792066074360228252100000000000000)
      constant := (915776234099340226549585422641223026780294825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49743693530738551289/100000000000000000000)
  centralHi := (4974369353073855129/10000000000000000000)
  directionLo := (562785648269609991/800000000000000000)
  directionHi := (17587051508425312219/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree003.table
  base := (71034637791992842573783906978185209705973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-98636633668979501109452811731700000000000000)
      constant := (865288655667866497918449856744988144959476039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree003.table
  base := (3526203122630667802153934298611727181433/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-37490578111003787905031181395950000000000000)
      constant := (326423219963120667099381937278334910041307930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562785648269609991/800000000000000000)
  centralHi := (17587051508425312219/25000000000000000000)
  directionLo := (86158604551374444813/100000000000000000000)
  directionHi := (43079302275687222407/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree004.table
  base := (47175996228737326619102323946534212739009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-342977765063268034778087843109300000000000000)
      constant := (2023461025041277135530693218700570350900412961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree004.table
  base := (23378407205380680003108726005818776445743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-43468298279611542772882248665850000000000000)
      constant := (254579466358198146925829863284290528226730303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86158604551374444813/100000000000000000000)
  centralHi := (43079302275687222407/50000000000000000000)
  directionLo := (99487387061477102579/100000000000000000000)
  directionHi := (4974369353073855129/5000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree005.table
  base := (31783337991515113208686671233089728248461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-390045629119597566227817251023500000000000000)
      constant := (1742081127883664341814913421651468096296034669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree005.table
  base := (6290752992546454012563691570536432714661/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-98892036896438595281466631871500000000000000)
      constant := (439098551293206312637717222661095417664148905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99487387061477102579/100000000000000000000)
  centralHi := (4974369353073855129/5000000000000000000)
  directionLo := (55615140093323962593/50000000000000000000)
  directionHi := (111230280186647925187/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree006.table
  base := (21509033317688027933198389334291877264633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-145704497725309032559182219645900000000000000)
      constant := (548949460899023248845947482800210074274562419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree006.table
  base := (21253785326020022064485223506603893962179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-110847477233654105017168766411300000000000000)
      constant := (416041794570440856437487844843209444074419859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55615140093323962593/50000000000000000000)
  centralHi := (111230280186647925187/100000000000000000000)
  directionLo := (24369333414338802873/20000000000000000000)
  directionHi := (60923333535847007183/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree007.table
  base := (14381960982491599881339365413056320351109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-484181357232256629127276066851900000000000000)
      constant := (1676009532630847240519421721875041460279893861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree007.table
  base := (7091984926327857370837361278221358780697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-61401458785434807376435450475550000000000000)
      constant := (212180638455269129147460640433091382901900937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24369333414338802873/20000000000000000000)
  centralHi := (60923333535847007183/50000000000000000000)
  directionLo := (32902360594036678853/25000000000000000000)
  directionHi := (131609442376146715413/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree008.table
  base := (4616760745788706980134771803380774303381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-265624610644293080288502737383050000000000000)
      constant := (896476762063277663658032565977316278150623349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree008.table
  base := (9078127756076541612455469789705110198473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-134758357908085124488573035490900000000000000)
      constant := (454819601093134528066638236361854177882104633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32902360594036678853/25000000000000000000)
  centralHi := (131609442376146715413/100000000000000000000)
  directionLo := (140696412067402497751/100000000000000000000)
  directionHi := (17587051508425312219/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree009.table
  base := (2682230257410317146505932458724753816523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-96386180890819282004455813780050000000000000)
      constant := (329295569712618837289659732882062604105949689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree009.table
  base := (2620180947765445090002037035902472724151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-73356899122650317112137585015350000000000000)
      constant := (250952282933168071582650315076583486448000071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140696412067402497751/100000000000000000000)
  centralHi := (17587051508425312219/12500000000000000000)
  directionLo := (149231080592215653869/100000000000000000000)
  directionHi := (14923108059221565387/10000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree010.table
  base := (2351186077678785933884662447248712907049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-625384949401245223476464290594500000000000000)
      constant := (2211198502107879132211840575644854926664938121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree010.table
  base := (450028511414243815107899431053524334009/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-158669238582516143959977304570500000000000000)
      constant := (562285155365964628408793858281874831248426445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149231080592215653869/100000000000000000000)
  centralHi := (14923108059221565387/10000000000000000000)
  directionLo := (39325842696629213483/25000000000000000000)
  directionHi := (157303370786516853933/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree011.table
  base := (-67051069456390863526717836441959881629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-672452813457574754926193698508700000000000000)
      constant := (2491059762382076483142286970824709838868445059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree011.table
  base := (-150868716265981241702730984596752125259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-170624678919731653695679439110300000000000000)
      constant := (633915070674412024724722553682409126415823461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39325842696629213483/25000000000000000000)
  centralHi := (157303370786516853933/100000000000000000000)
  directionLo := (164981167127889007391/100000000000000000000)
  directionHi := (5155661472746531481/3125000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree012.table
  base := (-1027025470837280074718174031436877761453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-119920112918984047729320517737150000000000000)
      constant := (468370918070926831916690152849104685537146321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree012.table
  base := (-1062355663652423753457535387650861353923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-91290059628473581715690786825050000000000000)
      constant := (357755398840954172516813618654217527215575917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164981167127889007391/100000000000000000000)
  centralHi := (5155661472746531481/3125000000000000000)
  directionLo := (86158604551374444813/50000000000000000000)
  directionHi := (172317209102748889627/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree013.table
  base := (-74305769296607531156039125337895724571/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-383294270785116908912826257168550000000000000)
      constant := (1582695658143116091129070376425426621122878525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree013.table
  base := (-3775630473264012128200714032558851527793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-194535559594162673167083708189900000000000000)
      constant := (806246610181284802030922526787701337048351647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86158604551374444813/50000000000000000000)
  centralHi := (172317209102748889627/100000000000000000000)
  directionLo := (179353437656044176493/100000000000000000000)
  directionHi := (89676718828022088247/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree014.table
  base := (-5120663283530928979917597524788218431043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-813656405626563349275381922251300000000000000)
      constant := (3554367299998194567540935026608509904773853853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree014.table
  base := (-1034538080139240918544094283075807185693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-206490999931378182902785842729700000000000000)
      constant := (905575450275597225448807640890182656410628735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179353437656044176493/100000000000000000000)
  centralHi := (89676718828022088247/50000000000000000000)
  directionLo := (186123858344707021563/100000000000000000000)
  directionHi := (46530964586176755391/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree015.table
  base := (-6317987510482738743410466104142559037697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-286908089894297626908370443388500000000000000)
      constant := (1325218517960821846891763789719439255969330229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree015.table
  base := (-1590786208797503350711684614845532278779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-109223220134296846319243988634750000000000000)
      constant := (506561510602229202879995417289117077639583082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186123858344707021563/100000000000000000000)
  centralHi := (46530964586176755391/25000000000000000000)
  directionLo := (38531299324679206039/20000000000000000000)
  directionHi := (48164124155849007549/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree016.table
  base := (-7341053051407565188972928028226730347401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-907792133739222412174840738079700000000000000)
      constant := (4428197411324688103276658645357284764946274071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree016.table
  base := (-7380414817205661996590858142580838007079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-230401880605809202374190111809300000000000000)
      constant := (1128624594906382913111984260123017182145927241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38531299324679206039/20000000000000000000)
  centralHi := (48164124155849007549/25000000000000000000)
  directionLo := (198974774122954205159/100000000000000000000)
  directionHi := (4974369353073855129/2500000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree017.table
  base := (-4107256915560285313083071143448010694497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-477429998897775971812285072996950000000000000)
      constant := (2455610244757164017674397652606117272952103487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree017.table
  base := (-824890706131599396667890511441120420381/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-121178660471512356054946123174550000000000000)
      constant := (625943422897619626703402340113174425750810495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198974774122954205159/100000000000000000000)
  centralHi := (4974369353073855129/2500000000000000000)
  directionLo := (205098502635588948323/100000000000000000000)
  directionHi := (51274625658897237081/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree018.table
  base := (-4478443062045388771421033537485250879271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-166987976975313579179049925651350000000000000)
      constant := (904024115348090888561631225072941525067772947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree018.table
  base := (-4493485322864238595644902400906166248529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-127156380640120110922797190444450000000000000)
      constant := (691382215411273036790698413290722257145401791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205098502635588948323/100000000000000000000)
  centralHi := (51274625658897237081/25000000000000000000)
  directionLo := (211044618101103746627/100000000000000000000)
  directionHi := (52761154525275936657/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree019.table
  base := (-1197803588453009380883147994479444776633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-524497862954105503262014480911150000000000000)
      constant := (2983261652906561895736541319067113898371458972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree019.table
  base := (-9608748270143535139093701721652904523071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-266268201617455731581296515428700000000000000)
      constant := (1521145325663976319340424484470187343272754609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211044618101103746627/100000000000000000000)
  centralHi := (52761154525275936657/25000000000000000000)
  directionLo := (216827733178947308709/100000000000000000000)
  directionHi := (21682773317894730871/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree020.table
  base := (-80818796646702566334303576999721247263/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-1096063589964540537973758369736500000000000000)
      constant := (6538005195283715717749333730811966630562184125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree020.table
  base := (-10125364308734533803136213570416503683487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-278223641954671241316998649968500000000000000)
      constant := (1666941414151702758652973316118730874323099473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216827733178947308709/100000000000000000000)
  centralHi := (21682773317894730871/10000000000000000000)
  directionLo := (222460560373295850373/100000000000000000000)
  directionHi := (111230280186647925187/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree021.table
  base := (-526280123430428548554782398658180732539/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-190521909003478344903914629608450000000000000)
      constant := (1189718308208943913532340422414726186100952230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree021.table
  base := (-2636427374978433080159152593297692680519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-145089541145943375526350392254150000000000000)
      constant := (910041136373380943446564741829177952555218002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222460560373295850373/100000000000000000000)
  centralHi := (111230280186647925187/50000000000000000000)
  directionLo := (227954240951294539361/100000000000000000000)
  directionHi := (113977120475647269681/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree022.table
  base := (-10859429164789144609760518004795762877647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-1190199318077199600873217185564900000000000000)
      constant := (7767210389563352114580119808363153544806197137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree022.table
  base := (-2719243985478014393700127220134307296803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-151067261314551130394201459524050000000000000)
      constant := (990255466419533266109510648403932303804046874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227954240951294539361/100000000000000000000)
  centralHi := (113977120475647269681/50000000000000000000)
  directionLo := (46663720817680575857/20000000000000000000)
  directionHi := (116659302044201439643/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree023.table
  base := (-5554870506200366074912591203279981146191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-618633591066764566161473296739550000000000000)
      constant := (4212260809873635371274406073981141470670982161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree023.table
  base := (-11125034071296237505425816852448172278913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-314089962966317770524105053587900000000000000)
      constant := (2148180894700571642619509528200358027378730127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46663720817680575857/20000000000000000000)
  centralHi := (116659302044201439643/50000000000000000000)
  directionLo := (47712474704144587757/20000000000000000000)
  directionHi := (119281186760361469393/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree024.table
  base := (-1410174490745109147038378351155074066733/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-214055841031643110628779333565550000000000000)
      constant := (1518348557700249894573518313143150246084429124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree024.table
  base := (-11294706959911597378888630560859739890817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-326045403303533280259807188127700000000000000)
      constant := (2323053954779190396659629119265830000324838543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47712474704144587757/20000000000000000000)
  centralHi := (119281186760361469393/50000000000000000000)
  directionLo := (24369333414338802873/10000000000000000000)
  directionHi := (243693334143388028731/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree025.table
  base := (-5689202780047410019708579031315061407989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-665701455123094097611202704653750000000000000)
      constant := (4911896943899141729188624617277930441149112619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree025.table
  base := (-5694987922387936736835929546569498812951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-169000421820374394997754661333750000000000000)
      constant := (1252549288848252652638758473561622999902615129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24369333414338802873/10000000000000000000)
  centralHi := (243693334143388028731/100000000000000000000)
  directionLo := (248718467653692756449/100000000000000000000)
  directionHi := (4974369353073855129/2000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree026.table
  base := (-11404094254776152362815969249455412686499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-1378470774302517726672134817221700000000000000)
      constant := (10565525096290590739327573760164411375944672829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree026.table
  base := (-1426767260726641650432835889687232344287/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-174978141988982149865605728603650000000000000)
      constant := (1347144322532278915244678411007849730403610692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248718467653692756449/100000000000000000000)
  centralHi := (4974369353073855129/2000000000000000000)
  directionLo := (126822031995707522621/50000000000000000000)
  directionHi := (253644063991415045243/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree027.table
  base := (-5680611796794573892409774578545868667863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-237589773059807876353644037522650000000000000)
      constant := (1889199742337718229360213118344145493501506691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree027.table
  base := (-5684965559136547855823387191576898430671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-180955862157589904733456795873550000000000000)
      constant := (1445301236829367473480195466534819387530655009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126822031995707522621/50000000000000000000)
  centralHi := (253644063991415045243/100000000000000000000)
  directionLo := (6461895341353083361/2500000000000000000)
  directionHi := (258475813654123334441/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree028.table
  base := (-562604583513241234125063256806266911437/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-736303251207588394785796816525050000000000000)
      constant := (6066370982013470147071516279265364639315902270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree028.table
  base := (-2251926266329409811012972032319913479437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-373867164652395319202615726286900000000000000)
      constant := (3094022032197876161992383784515569826646897615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6461895341353083361/2500000000000000000)
  centralHi := (258475813654123334441/100000000000000000000)
  directionLo := (32902360594036678853/12500000000000000000)
  directionHi := (10528755390091737233/4000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree029.table
  base := (-5539306613717658147643766322862672898057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-759837183235753160510661520482150000000000000)
      constant := (6479047819660280695507422567820835320776772247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree029.table
  base := (-5542566971093348287570489621898165886993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-192911302494805414469158930413350000000000000)
      constant := (1652266154337025866708957798387144628009128447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32902360594036678853/12500000000000000000)
  centralHi := (10528755390091737233/4000000000000000000)
  directionLo := (267877987778617546433/100000000000000000000)
  directionHi := (133938993889308773217/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree030.table
  base := (-433695399269543058495903271460199740477/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-522247410175945284157017482959500000000000000)
      constant := (4603736485457207403649272393858528352754967225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree030.table
  base := (-5424009058678659943010372383304955320867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-198889022663413169337009997683250000000000000)
      constant := (1761060397250884582785669484094341448903412493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267877987778617546433/100000000000000000000)
  centralHi := (133938993889308773217/50000000000000000000)
  directionLo := (2128573675031977011/781250000000000000)
  directionHi := (272457430404093057409/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree031.table
  base := (-10544739252751479708782303023816221640849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-1613810094584165383920781856792700000000000000)
      constant := (14692041674940098851949762248943461592213841679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree031.table
  base := (-84396803509510182444818441869147988097/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-409733485664041848409722129906300000000000000)
      constant := (3746777061038730486361082664461709848285457875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2128573675031977011/781250000000000000)
  centralHi := (272457430404093057409/100000000000000000000)
  directionLo := (34620145514498051691/12500000000000000000)
  directionHi := (276961164115984413529/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree032.table
  base := (-1018678821658796617739912563794701525477/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-830438979320247457685255632353450000000000000)
      constant := (7800278725830258841640983517911578979541655335) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree032.table
  base := (-10190979007472138115921679174011037406301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-421688926001257358145424264446100000000000000)
      constant := (3978492410224609029070639382824258572704689779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34620145514498051691/12500000000000000000)
  centralHi := (276961164115984413529/100000000000000000000)
  directionLo := (281392824134804995503/100000000000000000000)
  directionHi := (17587051508425312219/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree033.table
  base := (-390778422310498894235975673412028306193/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-569315274232274815606746890873700000000000000)
      constant := (5512242563925241974740934214076754709960662525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree033.table
  base := (-9773069958893558125331331713759404763829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-433644366338472867881126398985900000000000000)
      constant := (4217259585352595360475549247012911754865710491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281392824134804995503/100000000000000000000)
  centralHi := (17587051508425312219/6250000000000000000)
  directionLo := (142877881878758033649/50000000000000000000)
  directionHi := (285755763757516067299/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree034.table
  base := (-9293531904679421887700442878639423842243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-1755013686753153978269970080535300000000000000)
      constant := (17500528095623441386447647183743705490446369053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree034.table
  base := (-9296637766568729777134207219502670947131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-445599806675688377616828533525700000000000000)
      constant := (4463072531027179545087909634699719343427775349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (142877881878758033649/50000000000000000000)
  centralHi := (285755763757516067299/100000000000000000000)
  directionLo := (290053084049663870427/100000000000000000000)
  directionHi := (72513271012415967607/25000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree035.table
  base := (-8759650149947021326359992720033290156451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-1802081550809483509719699488449500000000000000)
      constant := (18491938365376141566840091039959077052688546621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree035.table
  base := (-547645027354131587629044790981403917691/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-228777623506451943676265334032750000000000000)
      constant := (2357963096796790135997986638317590396543756712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290053084049663870427/100000000000000000000)
  centralHi := (72513271012415967607/25000000000000000000)
  directionLo := (73571914908476375559/25000000000000000000)
  directionHi := (294287659633905502237/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree036.table
  base := (-4084178271372554089739476387003582285179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-308191569144302173528238149393950000000000000)
      constant := (3251823590706378556020750876195121590195875703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree036.table
  base := (-817065048594931497115831331677515524387/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-234755343675059698544116401302650000000000000)
      constant := (2487908177505137914099584173637111997656652865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73571914908476375559/25000000000000000000)
  centralHi := (294287659633905502237/100000000000000000000)
  directionLo := (298462161184431307739/100000000000000000000)
  directionHi := (14923108059221565387/5000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree037.table
  base := (-7520103275384067004643015257304976706159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-1896217278922142572619158304277900000000000000)
      constant := (20557523465476938656496287683920292384772744689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree037.table
  base := (-7522072405384010521891000447293358417093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-481466127687334906823934937145100000000000000)
      constant := (5242739494440564283908647424916589307978206347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298462161184431307739/100000000000000000000)
  centralHi := (14923108059221565387/5000000000000000000)
  directionLo := (151289537563707205913/50000000000000000000)
  directionHi := (302579075127414411827/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree038.table
  base := (-6815268156236815840884916054195447440647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-1943285142978472104068887712192100000000000000)
      constant := (21631672292733628378710581737689510827131970137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree038.table
  base := (-3408478618520989890164492064751193024713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-246710784012275208279818535842450000000000000)
      constant := (2758346336434058004273120045592405800051248327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151289537563707205913/50000000000000000000)
  centralHi := (302579075127414411827/100000000000000000000)
  directionLo := (38330090120035251319/12500000000000000000)
  directionHi := (306640720960282010553/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree039.table
  base := (-6054166857304724550577919600627402333639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-663451002344933878506205706702100000000000000)
      constant := (7577792712106736528783031805654848037429807923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree039.table
  base := (-6055614717987459056086069819931163898011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-505377008361765926295339206224700000000000000)
      constant := (5797673436865645186303495393057725250763854869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38330090120035251319/12500000000000000000)
  centralHi := (306640720960282010553/100000000000000000000)
  directionLo := (310649266532405602521/100000000000000000000)
  directionHi := (155324633266202801261/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree040.table
  base := (-2618531570284610490524295517652313844411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1018710435545565583484173264010250000000000000)
      constant := (11931316366418783063191467381257470659568447781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree040.table
  base := (-2619151708266912663112504860891323953173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-258666224349490718015520670382250000000000000)
      constant := (3042839869156770779072549635166879822966916667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310649266532405602521/100000000000000000000)
  centralHi := (155324633266202801261/50000000000000000000)
  directionLo := (62921348314606741573/20000000000000000000)
  directionHi := (157303370786516853933/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree041.table
  base := (-2182088699296468800072830144222078783077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1042244367573730349209037967967350000000000000)
      constant := (12509714588803551643113433457178466493804980667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree041.table
  base := (-1091309797344870596470933370943782693689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-264643944518098472883371737652150000000000000)
      constant := (3190354933705448533804882091132708594566578862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62921348314606741573/20000000000000000000)
  centralHi := (157303370786516853933/50000000000000000000)
  directionLo := (7962876242652590367/2500000000000000000)
  directionHi := (318515049706103614681/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree042.table
  base := (-858923447092541152377558552057007892931/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-355259433200631704977967557308150000000000000)
      constant := (4367293616862391158025612939340637333148243134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree042.table
  base := (-3436602239499550736305381181965114488713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-541243329373412455502445609844100000000000000)
      constant := (6682762396769945785207143216310254328134904327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7962876242652590367/2500000000000000000)
  centralHi := (318515049706103614681/100000000000000000000)
  directionLo := (161187989576892558837/50000000000000000000)
  directionHi := (12895039166151404707/4000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree043.table
  base := (-49035323815793366679925564229332500837/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1089312231630059880658767375881550000000000000)
      constant := (13707812741302466475986008522516181052031940675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree043.table
  base := (-2452543006898856149420653123067559818621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-553198769710627965238147744383900000000000000)
      constant := (6991836134755409485997773295338781858676703059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161187989576892558837/50000000000000000000)
  centralHi := (12895039166151404707/4000000000000000000)
  directionLo := (40773901537442147787/12500000000000000000)
  directionHi := (326191212299537182297/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree044.table
  base := (-1412523189421906159757956370509712338469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-2225692327316449292767264159677300000000000000)
      constant := (28655016493504182438231061335099901222148104699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree044.table
  base := (-353296771395342572983806964753525856901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-282577105023921737486924939461850000000000000)
      constant := (3653965043268591355204839369770574643374974358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40773901537442147787/12500000000000000000)
  centralHi := (326191212299537182297/100000000000000000000)
  directionLo := (329962334255778014783/100000000000000000000)
  directionHi := (5155661472746531481/1562500000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree045.table
  base := (-159036115116153654602919750952047343923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-378793365228796470702832261265250000000000000)
      constant := (4986988561282907412470318288855807769587412111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree045.table
  base := (-15931966395681582952806855256842406639/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-288554825192529492354776006731750000000000000)
      constant := (3815521710789835053511162325350105512970124810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329962334255778014783/100000000000000000000)
  centralHi := (5155661472746531481/1562500000000000000)
  directionLo := (333690840559943775559/100000000000000000000)
  directionHi := (8342271013998594389/2500000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree046.table
  base := (831496902899985915452611638644309407581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-2319828055429108355666722975505700000000000000)
      constant := (31216367292345569412558704701121687569430105149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree046.table
  base := (415506364601344529111255687772359243863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-294532545361137247222627074001650000000000000)
      constant := (3980587723251536771146173350612544857570638823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333690840559943775559/100000000000000000000)
  centralHi := (8342271013998594389/2500000000000000000)
  directionLo := (168689072052461254233/50000000000000000000)
  directionHi := (337378144104922508467/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree047.table
  base := (1018054592121863612049339763387500484159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1183447959742718943558226191709950000000000000)
      constant := (16269160958483711518209158468869867002668217311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree047.table
  base := (2035696004217335973059352661952928121493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-601020531059490004180956282543100000000000000)
      constant := (8298325582428433439340074439575929143650346053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168689072052461254233/50000000000000000000)
  centralHi := (337378144104922508467/100000000000000000000)
  directionLo := (34102558139494740659/10000000000000000000)
  directionHi := (341025581394947406591/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree048.table
  base := (1647850959905338110151092973891551862001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-402327297256961236427696965222350000000000000)
      constant := (5647965546237174627170164231616749476094876443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree048.table
  base := (205959342707129255819870292141972625079/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-306487985698352756958329208541450000000000000)
      constant := (4321246673032655676632605374809252521306006072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34102558139494740659/10000000000000000000)
  centralHi := (341025581394947406591/100000000000000000000)
  directionLo := (344634418205497779253/100000000000000000000)
  directionHi := (172317209102748889627/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree049.table
  base := (4610222719930253950843828667969181388979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-2461031647598096950015911199248300000000000000)
      constant := (35264779732396454024341302537324406483735323091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree049.table
  base := (460992222720800468628991009900548978539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-312465705866960511826180275811350000000000000)
      constant := (4496839166961815871894362824956311242295037095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344634418205497779253/100000000000000000000)
  centralHi := (172317209102748889627/50000000000000000000)
  directionLo := (348205854715169859029/100000000000000000000)
  directionHi := (34820585471516985903/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree050.table
  base := (5979627805182750215884417104527602288381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-2508099511654426481465640607162500000000000000)
      constant := (36669279910322201719528506378842745252092688349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree050.table
  base := (747421463398675369642648233151810563273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-318443426035568266694031343081250000000000000)
      constant := (4675940104566742369113992725806681965886741732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (348205854715169859029/100000000000000000000)
  centralHi := (34820585471516985903/10000000000000000000)
  directionLo := (175870515084253122189/50000000000000000000)
  directionHi := (351741030168506244379/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree051.table
  base := (7403880590869286605526784780669703261657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-851722458570252004305123338358900000000000000)
      constant := (12700430888346086562292976195234733711161484051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree051.table
  base := (370183120800946063660482749788497999009/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-324421146204176021561882410351150000000000000)
      constant := (4858549345221013755756128942282446926501502890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175870515084253122189/50000000000000000000)
  centralHi := (351741030168506244379/100000000000000000000)
  directionLo := (7104820542422786919/2000000000000000000)
  directionHi := (355241027121139345951/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree052.table
  base := (2220737626054020512656146044008574605173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1301117619883542772182549711495450000000000000)
      constant := (19780408519365099069638641618221689267610929834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree052.table
  base := (8882764708269388935597602189721245007261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-660797732745567552859466955242100000000000000)
      constant := (10089333543027831444535574145868381981702514381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7104820542422786919/2000000000000000000)
  centralHi := (355241027121139345951/100000000000000000000)
  directionLo := (179353437656044176493/50000000000000000000)
  directionHi := (358706875312088352987/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree053.table
  base := (2083362399208898624786954348181253535429/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-2649303103823415075814828830905100000000000000)
      constant := (41047852230967799356791473019691252460057275705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree053.table
  base := (5208326916105943361311158825567421933891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-336376586541391531297584544890950000000000000)
      constant := (5234292285416225884071492745615119549138350611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179353437656044176493/50000000000000000000)
  centralHi := (358706875312088352987/100000000000000000000)
  directionLo := (181069777601234533813/50000000000000000000)
  directionHi := (362139555202469067627/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree054.table
  base := (12005443714932086767639614245378965665651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-898790322626581535754852746273100000000000000)
      constant := (14187465857610783311384375390362692538446393393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree054.table
  base := (12005309121606142227139318566559857436739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-684708613419998572330871224321700000000000000)
      constant := (10854851610158599284597500472285120630756409619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181069777601234533813/50000000000000000000)
  centralHi := (362139555202469067627/100000000000000000000)
  directionLo := (73108000243016408619/20000000000000000000)
  directionHi := (45692500151885255387/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree055.table
  base := (6824413908574079920305992900330049332453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1371719415968037069357143823366750000000000000)
      constant := (22052226252648805336326935481831940115536420037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree055.table
  base := (1364871332098232932360108417207462640987/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-348332026878607041033286679430750000000000000)
      constant := (5624067262162848750579328588531001557896290135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73108000243016408619/20000000000000000000)
  centralHi := (45692500151885255387/12500000000000000000)
  directionLo := (368909104705213560471/100000000000000000000)
  directionHi := (46113638088151695059/12500000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree056.table
  base := (767347469502013896424829162777022470403/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1395253347996201835082008527323850000000000000)
      constant := (22837008280582546727263185052497213369752555870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree056.table
  base := (191835650279557869676487475404119257939/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-354309747047214795901137746700650000000000000)
      constant := (5824216599604084979989969937388241145685392760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368909104705213560471/100000000000000000000)
  centralHi := (46113638088151695059/12500000000000000000)
  directionLo := (372247716689414043127/100000000000000000000)
  directionHi := (46530964586176755391/12500000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree057.table
  base := (17099795970218991311214163602036047558487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-945858186682911067204582154187300000000000000)
      constant := (15757029783323090069830086996960862444653279741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree057.table
  base := (8549856597514616423823037497902452274719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-360287467215822550768988813970550000000000000)
      constant := (6027873769755326680506662698021685324468049199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372247716689414043127/100000000000000000000)
  centralHi := (46530964586176755391/12500000000000000000)
  directionLo := (375556650355924735473/100000000000000000000)
  directionHi := (187778325177962367737/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree058.table
  base := (2363419642619352559748823289958691516171/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1442321212052531366531737935238050000000000000)
      constant := (24447835272682211536976250286481163386040485036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree058.table
  base := (4726821698232503886011780890310775177727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-366265187384430305636839881240450000000000000)
      constant := (6235038732829208179611071444490603300365551134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (375556650355924735473/100000000000000000000)
  centralHi := (187778325177962367737/50000000000000000000)
  directionLo := (3788366833777351387/1000000000000000000)
  directionHi := (378836683377735138701/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree059.table
  base := (10384812097882102653928404477856859927023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2655000000000000000000000000000000000000000
      center := (9021)
      previous := (0)
      next := (7440)
      square := (363926783940692253477289236450000000000000)
      linear := (-24845002442045697156891570155850000000000000)
      constant := (428370846394789225363417370510441992621249213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree059.table
  base := (20769564426963395029635989883784685765391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-744485815106076121009381897020700000000000000)
      constant := (12891422911201369476564964328984858495947662111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3788366833777351387/1000000000000000000)
  centralHi := (378836683377735138701/100000000000000000000)
  directionLo := (191044280023455807951/50000000000000000000)
  directionHi := (382088560046911615903/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree060.table
  base := (11343294928651170080436585403687393881729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-496463025369620299327155781050750000000000000)
      constant := (8704559518273241891731473133755707454306895947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree060.table
  base := (22686539091362821141436977565165686486021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-756441255443291630745084031560500000000000000)
      constant := (13319783820646835869200859224883677402655772341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191044280023455807951/50000000000000000000)
  centralHi := (382088560046911615903/100000000000000000000)
  directionLo := (38531299324679206039/10000000000000000000)
  directionHi := (385312993246792060391/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree061.table
  base := (24658248042469973923592317883152824798287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-3025846016274051327412664094218700000000000000)
      constant := (53934462059949974908336075666668894848105533423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree061.table
  base := (24658204935282307435166997698671494220107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-768396695780507140480786166100300000000000000)
      constant := (13755160147650264478504661229447576905717467547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38531299324679206039/10000000000000000000)
  centralHi := (385312993246792060391/100000000000000000000)
  directionLo := (388510666276850711041/100000000000000000000)
  directionHi := (194255333138425355521/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree062.table
  base := (3335574208267029695191853291055448135633/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1536456940165190429431196751066450000000000000)
      constant := (27834537283102317135371877221347604538564985028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree062.table
  base := (3335569634013143997951057882585786855729/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-390176068058861325108244150320050000000000000)
      constant := (7098775926752382204255439917139148070736917636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388510666276850711041/100000000000000000000)
  centralHi := (194255333138425355521/50000000000000000000)
  directionLo := (78336446908693147527/20000000000000000000)
  directionHi := (97920558635866434409/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree063.table
  base := (143828112385643725083082151721826422999/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-519996957397785065052020485007850000000000000)
      constant := (9571865749203074959133025527900003333537855700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree063.table
  base := (28765591420246819279627822236835357439091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-792307576454938159952190435179900000000000000)
      constant := (14646958905880104553467510178622572866275039811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78336446908693147527/20000000000000000000)
  centralHi := (97920558635866434409/25000000000000000000)
  directionLo := (98707081782110036559/25000000000000000000)
  directionHi := (394828327128440146237/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree064.table
  base := (1236053236847440517699838738047678069547/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-3167049608443039921761852317961300000000000000)
      constant := (59220821735639963348741749592784992656020949075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree064.table
  base := (30901304570250144700194537035010560930057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-804263016792153669687892569719700000000000000)
      constant := (15103381277769974712395527369460718653126981497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98707081782110036559/25000000000000000000)
  centralHi := (394828327128440146237/100000000000000000000)
  directionLo := (198974774122954205159/50000000000000000000)
  directionHi := (397949548245908410319/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree065.table
  base := (33091716026439430501554983277919141912199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-3214117472499369453211581725875500000000000000)
      constant := (61037956194363503343642795067873928796967282471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree065.table
  base := (517057713653597148179482900715931707587/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-408109228564684589711797352129750000000000000)
      constant := (7783409473306555053575270853380268641785492064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198974774122954205159/50000000000000000000)
  centralHi := (397949548245908410319/100000000000000000000)
  directionLo := (40104647859718532371/10000000000000000000)
  directionHi := (401046478597185323711/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree066.table
  base := (35336775307720798735551266538998163311273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-1087061778851899661553770377929900000000000000)
      constant := (20960865931177078411446173149762957819459623939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree066.table
  base := (7067351270248715382816758453995876181883/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-828173897466584689159296838799300000000000000)
      constant := (16037271893559562785405702373855906676183476215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40104647859718532371/10000000000000000000)
  centralHi := (401046478597185323711/100000000000000000000)
  directionLo := (40411967663216136243/10000000000000000000)
  directionHi := (404119676632161362431/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree067.table
  base := (37636506686600426624203947927599713123809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-3308253200612028516111040541703900000000000000)
      constant := (64754746468028035230854543351187171412455812161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree067.table
  base := (7527298122791032105183057202348847042011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-840129337803800198894998973339100000000000000)
      constant := (16514740102858146517367269606541626087098845655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40411967663216136243/10000000000000000000)
  centralHi := (404119676632161362431/100000000000000000000)
  directionLo := (407169679725004458403/100000000000000000000)
  directionHi := (101792419931251114601/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree068.table
  base := (19995454212284808997461840163171553327813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1677660532334179023780384974809050000000000000)
      constant := (33327201081694082195399907558864201594207053477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree068.table
  base := (7998178960015268323457619672916351079827/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-852084778141015708630701107878900000000000000)
      constant := (16999223561345041490931130866557452084516548335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407169679725004458403/100000000000000000000)
  centralHi := (101792419931251114601/25000000000000000000)
  directionLo := (410197005271177896647/100000000000000000000)
  directionHi := (51274625658897237081/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree069.table
  base := (8479995813441314194294302251450958899707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-1134129642908229193003499785844100000000000000)
      constant := (22860521611348680694397881535576711818948201005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree069.table
  base := (21199983760232361403335495433076495752759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-432020109239115609183201621209350000000000000)
      constant := (8745361129008425388219088607021598922857604039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410197005271177896647/100000000000000000000)
  centralHi := (51274625658897237081/12500000000000000000)
  directionLo := (103300537928029078683/25000000000000000000)
  directionHi := (413202151712116314733/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree070.table
  base := (448637173975199942089586656615497433261/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1724728396390508555230114382723250000000000000)
      constant := (35268117220937274070746005692187845954331693450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree070.table
  base := (22431853806862375443971029810910026174551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-437997829407723364051052688479250000000000000)
      constant := (8994618091837080098471358524124718317328618471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103300537928029078683/25000000000000000000)
  centralHi := (413202151712116314733/100000000000000000000)
  directionLo := (208092799746653192511/50000000000000000000)
  directionHi := (416185599493306385023/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree071.table
  base := (47382122396961614870704864307565206744101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-3496524656837346641909958173360700000000000000)
      constant := (72518410954963583725994558982616310362085940229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree071.table
  base := (47382114108639071331507192398913094204361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-887951099152662237837807511498300000000000000)
      constant := (18494765330623957087215835406181190619192743481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208092799746653192511/50000000000000000000)
  centralHi := (416185599493306385023/100000000000000000000)
  directionLo := (419147811960986942147/100000000000000000000)
  directionHi := (104786952990246735537/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree072.table
  base := (24977596606423407830085220249992323590087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-590598753482279362226614596879150000000000000)
      constant := (12421349057766565410236332697259069835251278541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree072.table
  base := (624439827410041916321058332895526653597/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-449953269744938873786754823019050000000000000)
      constant := (9503654846215593371369890681697418664925673480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419147811960986942147/100000000000000000000)
  centralHi := (104786952990246735537/25000000000000000000)
  directionLo := (211044618101103746627/50000000000000000000)
  directionHi := (84417847240441498651/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree073.table
  base := (52582929131129916804387909485126287020053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-3590660384950005704809416989189100000000000000)
      constant := (76565284594411637246155024657341921446051240437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree073.table
  base := (26291461593220011497940255412626832453299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-455930989913546628654605890288950000000000000)
      constant := (9763434631855665500664578035840217139862581379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211044618101103746627/50000000000000000000)
  centralHi := (84417847240441498651/20000000000000000000)
  directionLo := (425010303832557627937/100000000000000000000)
  directionHi := (212505151916278813969/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree074.table
  base := (55265329553653818944286095621910587635901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-3637728249006335236259146397103300000000000000)
      constant := (78629981679660654314385303542319436800045142429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree074.table
  base := (27632662260267784291128528962822440886641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-461908710082154383522456957558850000000000000)
      constant := (10026722019978616917929512685151216554263083361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (425010303832557627937/100000000000000000000)
  centralHi := (212505151916278813969/50000000000000000000)
  directionLo := (213955715867748547/50000000000000000)
  directionHi := (427911431735497094001/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree075.table
  base := (14500598494784611815274845105070124806447/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-614132685510444127951479300836250000000000000)
      constant := (13453697597773640033685287462801994626707452042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree075.table
  base := (58002389718587354656982319502973980571437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-935772860501524276780616049657500000000000000)
      constant := (20587034017394517871263952078908056900106352477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213955715867748547/50000000000000000)
  centralHi := (427911431735497094001/100000000000000000000)
  directionLo := (430793022756872224067/100000000000000000000)
  directionHi := (107698255689218056017/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree076.table
  base := (1215882439745867350678256953035929517109/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1865931988559497149579302606465850000000000000)
      constant := (41420948151093957947813622475149365896037696525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree076.table
  base := (60794118381363823852761362785165216699813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-947728300838739786516318184197300000000000000)
      constant := (21127639192860869941637593035009693681479218773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430793022756872224067/100000000000000000000)
  centralHi := (107698255689218056017/25000000000000000000)
  directionLo := (216827733178947308709/50000000000000000000)
  directionHi := (433655466357894617419/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree077.table
  base := (31820256612770496572786349533559081984781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1889465920587661915304167310422950000000000000)
      constant := (42494556907626489091901526358713072479501203949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree077.table
  base := (254562040696721692785020341328822657243/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-479841870587977648126010159368550000000000000)
      constant := (10837629781852626851439064604090000533502725375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216827733178947308709/50000000000000000000)
  centralHi := (433655466357894617419/100000000000000000000)
  directionLo := (27281196201848667311/6250000000000000000)
  directionHi := (436499139229578676977/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree078.table
  base := (16635391849480309283146589866920122907729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-637666617538608893676344004793350000000000000)
      constant := (14527306352760815583693314864966393687050827894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree078.table
  base := (16635391204068947443555417243003028515783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-485819590756585402993861226638450000000000000)
      constant := (11114947563851879199674886078338953977747034286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27281196201848667311/6250000000000000000)
  centralHi := (436499139229578676977/100000000000000000000)
  directionLo := (439324405871382418827/100000000000000000000)
  directionHi := (109831101467845604707/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree079.table
  base := (69497284255819016587212384781482574010833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-3873067569287982893507793436674300000000000000)
      constant := (89366069198334799918281122666083667561185387057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree079.table
  base := (17374320517985337708946622571654566870877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-491797310925193157861712293908350000000000000)
      constant := (11395772941494668213146421994204851648368433434) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439324405871382418827/100000000000000000000)
  centralHi := (109831101467845604707/25000000000000000000)
  directionLo := (442131619136567964501/100000000000000000000)
  directionHi := (221065809568283982251/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree080.table
  base := (36253831795107485190001310655670600558159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-1960067716672156212478761422294250000000000000)
      constant := (45797903527007164933671135969551504244886563311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree080.table
  base := (72507661743114779908684467874835248404443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-995550062187601825459126722356500000000000000)
      constant := (23360211827993136095720532993596570002611593003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442131619136567964501/100000000000000000000)
  centralHi := (221065809568283982251/50000000000000000000)
  directionLo := (222460560373295850373/50000000000000000000)
  directionHi := (444921120746591700747/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree081.table
  base := (75572705225209012357646673106766275067331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-1322401099133547318802417417500900000000000000)
      constant := (31284350559364236516748758538041160210528137633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree081.table
  base := (37786351831597787474149692536342138255813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-503752751262408667597414428448150000000000000)
      constant := (11967946480697757415468717060021566077124294773) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222460560373295850373/50000000000000000000)
  centralHi := (444921120746591700747/100000000000000000000)
  directionLo := (55961655222080870201/12500000000000000000)
  directionHi := (447693241776646961609/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree082.table
  base := (15738481802521500884177610047612163715953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-4014271161456971487856981660416900000000000000)
      constant := (96137803065927180478981527118137607385285457685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree082.table
  base := (39346203845940474910683013354388595699117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-509730471431016422465265495718050000000000000)
      constant := (12259294641042567131490976799188412066532705757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55961655222080870201/12500000000000000000)
  centralHi := (447693241776646961609/100000000000000000000)
  directionLo := (56306037889289029259/12500000000000000000)
  directionHi := (450448303114312234073/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree083.table
  base := (5116673426712451796520881600584884727821/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-2030669512756650509653355534165550000000000000)
      constant := (49225030606800633105148150105139490829103232872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree083.table
  base := (1279168339232086894805067605258805531909/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-515708191599624177333116562987950000000000000)
      constant := (12554150394562401357944389672721459955784038048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56306037889289029259/12500000000000000000)
  centralHi := (450448303114312234073/100000000000000000000)
  directionLo := (453186615893103525701/100000000000000000000)
  directionHi := (226593307946551762851/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree084.table
  base := (8509580256397407848909389538259253732571/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-684734481594938425126073412707550000000000000)
      constant := (16798304352967717951172496751840806933646194765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree084.table
  base := (85095801620180419095625638561737104271981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-1043371823536463864401935260515700000000000000)
      constant := (25705027481722950974353822931567919602938361501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (453186615893103525701/100000000000000000000)
  centralHi := (226593307946551762851/50000000000000000000)
  directionLo := (455908481902589078723/100000000000000000000)
  directionHi := (113977120475647269681/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree085.table
  base := (44189746066481200689357504201006894208541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-2077737376812980041103084942079750000000000000)
      constant := (51578548887871221566514295215668344988659380989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree085.table
  base := (11047436416913194633063753895864352090327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-527663631936839687068818697527750000000000000)
      constant := (13154384679604905614890428271581566131629920668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455908481902589078723/100000000000000000000)
  centralHi := (113977120475647269681/25000000000000000000)
  directionLo := (57326774247074583281/12500000000000000000)
  directionHi := (458614193976596666249/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree086.table
  base := (45858921729296498652763322760722615802647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-2101271308841144806827949646036850000000000000)
      constant := (52775938092517918280051955752351978830481127863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree086.table
  base := (91717842784538434784773581285749919154073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-1067282704210894883873339529595300000000000000)
      constant := (26919526421017522711745411704035825109619412233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57326774247074583281/12500000000000000000)
  centralHi := (458614193976596666249/100000000000000000000)
  directionLo := (230652018180463507899/50000000000000000000)
  directionHi := (461304036360927015799/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree087.table
  base := (19022171295296907766703363124890613518861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104430000000000000000000000000000000000000000
      center := (354826)
      previous := (0)
      next := (292640)
      square := (14314453501667228636773376633700000000000000)
      linear := (-1416536827246206381701876233329300000000000000)
      constant := (35991387114556495127006041353819963384887327115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree087.table
  base := (19022171181391246157853110096706633423781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-1079238144548110393609041664135100000000000000)
      constant := (27537298666663515751406187415044666216748846505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230652018180463507899/50000000000000000000)
  centralHi := (461304036360927015799/100000000000000000000)
  directionLo := (463978285061880363327/100000000000000000000)
  directionHi := (7249660704091880677/1562500000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree088.table
  base := (98558531131799194467799388046342546543577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-4296678345794948676555358107902100000000000000)
      constant := (110423953249925375172867940514010265640663723833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree088.table
  base := (98558530650651702711630562836747548444453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-1091193584885325903344743798674900000000000000)
      constant := (28162086095736633081979282743499477331228512213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463978285061880363327/100000000000000000000)
  centralHi := (7249660704091880677/1562500000000000000)
  directionLo := (46663720817680575857/10000000000000000000)
  directionHi := (466637208176805758571/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree089.table
  base := (6378804211106183880975381546353481016199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-2171873104925639104002543757908150000000000000)
      constant := (56450625951168058770441222053024465654051987768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree089.table
  base := (2041217339425391479096808918562912492499/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445000000000000000000000000000000000000000
      center := (1519)
      previous := (0)
      next := (1240)
      square := (60997144577630151712765992550000000000000)
      linear := (-6197466433834502320676662546150000000000000)
      constant := (161763419707222115491795716492602480295810275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46663720817680575857/10000000000000000000)
  centralHi := (466637208176805758571/100000000000000000000)
  directionLo := (14665033318993551173/3125000000000000000)
  directionHi := (469281066207793637537/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree090.table
  base := (26404466293513710695158521871107901846977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-731802345651267956575802820621750000000000000)
      constant := (19234342883274085492854366994272459637975961622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree090.table
  base := (105617864830783826044383775009612527433471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-1115104465559756922816148067754500000000000000)
      constant := (29432706502809022085750646796166140829800523791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14665033318993551173/3125000000000000000)
  centralHi := (469281066207793637537/100000000000000000000)
  directionLo := (471910112359550561797/100000000000000000000)
  directionHi := (235955056179775280899/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree091.table
  base := (5461476224318385977929390710999689288303/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-2218940968981968635452273165822350000000000000)
      constant := (58969184720384868353242399841158392657132446870) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree091.table
  base := (109229524196476139860541185780999821809719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-1127059905896972432551850202294300000000000000)
      constant := (30078539480247927860865013440326699588554784199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471910112359550561797/100000000000000000000)
  centralHi := (235955056179775280899/50000000000000000000)
  directionLo := (474524592822420191477/100000000000000000000)
  directionHi := (237262296411210095739/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree092.table
  base := (112895845284865516456836417196241251082449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-4484949802020266802354275739558900000000000000)
      constant := (120498188324779060047391684800289442155162044721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree092.table
  base := (22579169008016458821028205574331379067793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-1139015346234187942287552336834100000000000000)
      constant := (30731387639978372985979919825578994267979941765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474524592822420191477/100000000000000000000)
  centralHi := (237262296411210095739/50000000000000000000)
  directionLo := (477124747041445877571/100000000000000000000)
  directionHi := (119281186760361469393/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree093.table
  base := (3644275860742135018496378458219611090147/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-755336277679432722300667524578850000000000000)
      constant := (20514252325144032918186636307964398377830481936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree093.table
  base := (58308413668539405104785391123717268857991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-575485393285701726011627235686950000000000000)
      constant := (15695625490903053493676693094326764486624146711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477124747041445877571/100000000000000000000)
  centralHi := (119281186760361469393/25000000000000000000)
  directionLo := (239855403986153581253/50000000000000000000)
  directionHi := (479710807972307162507/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree094.table
  base := (30098117810139199876392597572557028944917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-2289542765066462932626867277693650000000000000)
      constant := (62850173159160760332543744192324578319630609386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree094.table
  base := (15049058883260838565948277922857802308563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-581463113454309480879478302956850000000000000)
      constant := (16029064752780893483603756009581526608344510092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239855403986153581253/50000000000000000000)
  centralHi := (479710807972307162507/100000000000000000000)
  directionLo := (48228300232490445661/10000000000000000000)
  directionHi := (482283002324904456611/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree095.table
  base := (24844555271128758230361463421165862365793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-4626153394189255396703463963301500000000000000)
      constant := (128342685426535503575552807370823526510289644485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree095.table
  base := (31055694052093265148026794398400524727703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-587440833622917235747329370226750000000000000)
      constant := (16366011605548514699577277630676961112736270926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48228300232490445661/10000000000000000000)
  centralHi := (482283002324904456611/100000000000000000000)
  directionLo := (242420775397656377257/50000000000000000000)
  directionHi := (96968310159062550903/20000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree096.table
  base := (32026935717933028511092223098972969291489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 52215000000000000000000000000000000000000000
      center := (177413)
      previous := (0)
      next := (146320)
      square := (7157226750833614318386688316850000000000000)
      linear := (-778870209707597488025532228535950000000000000)
      constant := (21835421879160811570288966748766749436622039254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree096.table
  base := (128107742747434211267771947313584078983667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (270382)
      previous := (0)
      next := (220720)
      square := (10857491734818167004872346673900000000000000)
      linear := (-1186837107583049981230360874993300000000000000)
      constant := (33412932098281108830867315908805299489629626307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242420775397656377257/50000000000000000000)
  centralHi := (96968310159062550903/20000000000000000000)
  directionLo := (24369333414338802873/5000000000000000000)
  directionHi := (487386668286776057461/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree097.table
  base := (66023685386772223866900889008404374756383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 156645000000000000000000000000000000000000000
      center := (532239)
      previous := (0)
      next := (438960)
      square := (21471680252500842955160064950550000000000000)
      linear := (-2360144561150957229801461389564950000000000000)
      constant := (66854941931565497515634772059639500656742723007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree097.table
  base := (66023685334323603501087881902430712074947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-599396273960132745483031504766550000000000000)
      constant := (17050428083499098423628597894171953670345655187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell197.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24369333414338802873/5000000000000000000)
  centralHi := (487386668286776057461/100000000000000000000)
  directionLo := (489918564120368803459/100000000000000000000)
  directionHi := (24495928206018440173/5000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 97
  qDenominator := 177
  table := BinomialMassData.Q97_177.Degree098.table
  base := (136041660047493459000202077622078029967843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 313290000000000000000000000000000000000000000
      center := (1064478)
      previous := (0)
      next := (877920)
      square := (42943360505001685910320129901100000000000000)
      linear := (-4767356986358243991052652187044100000000000000)
      constant := (136434743190608202841713669082219482600862553347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_177.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree098.table
  base := (68020829979489094529453673584736792561749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39605000000000000000000000000000000000000000
      center := (135191)
      previous := (0)
      next := (110360)
      square := (5428745867409083502436173336950000000000000)
      linear := (-605373994128740500350882572036450000000000000)
      constant := (17397897708572526126636540575949000133881613829) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell197.Kernel098
