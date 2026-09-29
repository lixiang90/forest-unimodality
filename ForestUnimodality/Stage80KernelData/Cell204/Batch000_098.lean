import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell204.Parameters
import ForestUnimodality.BinomialMassData.Q13_23.Batch000_049
import ForestUnimodality.BinomialMassData.Q13_23.Batch050_099
import ForestUnimodality.BinomialMassData.Q21_37.Batch000_049
import ForestUnimodality.BinomialMassData.Q21_37.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree000.table
  base := (191571016436045528552511999/10000000000000000000000000)
  polynomial :=
    { denominator := 46000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (90)
      square := (4367804778203091375932132230000000000000)
      linear := (-14405979615987775321883645860000000000000)
      constant := (881226675605809431341555195400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree000.table
  base := (191571016436045528552511999/10000000000000000000000000)
  polynomial :=
    { denominator := 74000000000000000000000000000000000000000
      center := (189)
      previous := (0)
      next := (144)
      square := (7026468556239755691716908370000000000000)
      linear := (-23174836773545551604769343340000000000000)
      constant := (1417625521626736911288588792600000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree001.table
  base := (62322219618084998401201436472676778960537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-2224502277004996040887796463800000000000000)
      constant := (67033766380433203800596280757442032140248146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree001.table
  base := (124372439963716444870922477079078587298277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-5762903199916275742142879275600000000000000)
      constant := (173117967716590870576529754414008586011341213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4954135886438745953/10000000000000000000)
  directionHi := (49541358864387459531/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree002.table
  base := (40725955954867751092611646617940439187463/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-2792316898171397919758973653700000000000000)
      constant := (45602716148168771832638892037380984660335854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree002.table
  base := (81105231395248769825352589633849232464467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-7238461596726624437403430033300000000000000)
      constant := (117574735682703230246853666278339599243855323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4954135886438745953/10000000000000000000)
  centralHi := (49541358864387459531/100000000000000000000)
  directionLo := (35031030802204649897/50000000000000000000)
  directionHi := (14012412320881859959/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree003.table
  base := (13354461902583112509775686516031343544471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-3360131519337799798630150843600000000000000)
      constant := (32511431556124113124277179506672322940100636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree003.table
  base := (829474156614604215684076391579978690547/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-8714019993536973132663980791000000000000000)
      constant := (83743937194978983384503300455221412950965952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35031030802204649897/50000000000000000000)
  centralHi := (14012412320881859959/20000000000000000000)
  directionLo := (85808150629121856989/100000000000000000000)
  directionHi := (8580815062912185699/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree004.table
  base := (17536776664450919980460902099843222389333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-3927946140504201677501328033500000000000000)
      constant := (24866974002507016462260966160434129287914314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree004.table
  base := (3479169815568084880220478984196285176449/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-2037915678069464365584906309740000000000000)
      constant := (12812619788133721551999823473849428813117362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85808150629121856989/100000000000000000000)
  centralHi := (8580815062912185699/10000000000000000000)
  directionLo := (99082717728774919061/100000000000000000000)
  directionHi := (49541358864387459531/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree005.table
  base := (183453801088881345370143911948187083331/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-899152152334120711274501044680000000000000)
      constant := (4164911941740011669456210158664774177052475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree005.table
  base := (1419186649582440870901336263789195830007/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-11665136787157670523185082306400000000000000)
      constant := (53721142304584565172129330826788545460473328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99082717728774919061/100000000000000000000)
  centralHi := (49541358864387459531/50000000000000000000)
  directionLo := (110777846118482144683/100000000000000000000)
  directionHi := (27694461529620536171/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree006.table
  base := (14769448287705033942718286818874894799823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-5063575382837005435243682413300000000000000)
      constant := (19208266774993718794530659196784819349106367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree006.table
  base := (14597362542439805413597713680145882959701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-13140695183968019218445633064100000000000000)
      constant := (49658560109401677792719637046119713771830669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110777846118482144683/100000000000000000000)
  centralHi := (27694461529620536171/25000000000000000000)
  directionLo := (121351050381857558451/100000000000000000000)
  directionHi := (30337762595464389613/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree007.table
  base := (4584319072010511230742276785432065560979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-5631390004003407314114859603200000000000000)
      constant := (19267928427004993367515863139337125363515782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree007.table
  base := (904048635297327631334552672583375805347/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-2923250716155673582741236764360000000000000)
      constant := (9985633710554870511908900660603282955040086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121351050381857558451/100000000000000000000)
  centralHi := (30337762595464389613/25000000000000000000)
  directionLo := (4096066098980453059/3125000000000000000)
  directionHi := (131074115167374497889/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree008.table
  base := (5224399968878347789808374821569310008041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-6199204625169809192986036793100000000000000)
      constant := (20524855349294775305162461388610164994253689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree008.table
  base := (5130880850535377121839187999945028605821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-16091811977588716608966734579500000000000000)
      constant := (53290369656770770930914640268724744161368949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4096066098980453059/3125000000000000000)
  centralHi := (131074115167374497889/100000000000000000000)
  directionLo := (35031030802204649897/25000000000000000000)
  directionHi := (140124123208818599589/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree009.table
  base := (235913934924555892150169471276874477449/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-1353403849267242214371442796600000000000000)
      constant := (4534700019473885405039394479120933197141042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree009.table
  base := (2291935994198566262494283828282546713323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-17567370374399065304227285337200000000000000)
      constant := (58955784275361128488485985623268806450539187) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35031030802204649897/25000000000000000000)
  centralHi := (140124123208818599589/100000000000000000000)
  directionLo := (4644502393536324331/3125000000000000000)
  directionHi := (148624076593162378593/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree010.table
  base := (102031648556820757345661348447719017271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-7334833867502612950728391172900000000000000)
      constant := (25518771180572179940768478360657686720272718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree010.table
  base := (156349479668034213668821980164008329059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-19042928771209413999487836094900000000000000)
      constant := (66421575553965830997130652002844527402481771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4644502393536324331/3125000000000000000)
  centralHi := (148624076593162378593/100000000000000000000)
  directionLo := (156663532391237173769/100000000000000000000)
  directionHi := (15666353239123717377/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree011.table
  base := (-1476377226562258827103439433499815869321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-7902648488669014829599568362800000000000000)
      constant := (28936063157248306076138689932028597405129191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree011.table
  base := (-1509927313969844395833432458178132334629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-20518487168019762694748386852600000000000000)
      constant := (75367330930554125323680993810504136833892899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156663532391237173769/100000000000000000000)
  centralHi := (15666353239123717377/10000000000000000000)
  directionLo := (164310098957520687909/100000000000000000000)
  directionHi := (16431009895752068791/10000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree012.table
  base := (-1416338743833074650156337895848555458817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-8470463109835416708470745552700000000000000)
      constant := (32845764031745165624396092613792228324571614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree012.table
  base := (-1428041104093990143896823580944898047491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-21994045564830111390008937610300000000000000)
      constant := (85588812277529596690018592498972869145969642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164310098957520687909/100000000000000000000)
  centralHi := (16431009895752068791/10000000000000000000)
  directionLo := (85808150629121856989/50000000000000000000)
  directionHi := (171616301258243713979/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree013.table
  base := (-1980511624669718202343019071723370521831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-9038277731001818587341922742600000000000000)
      constant := (37196991535360954547173120621866673987902802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree013.table
  base := (-12428885584521928151057495217278218823/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-4693920792328092017053897673600000000000000)
      constant := (19391157822182644816299233012152951579604032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85808150629121856989/50000000000000000000)
  centralHi := (171616301258243713979/100000000000000000000)
  directionLo := (44655977410427854221/25000000000000000000)
  directionHi := (35724781928342283377/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree014.table
  base := (-153840961841596988435726481074083572127/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-9606092352168220466213099932500000000000000)
      constant := (41957214142668060578408041597177913291034144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree014.table
  base := (-4934089680866224886293514062376993267171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-24945162358450808780530039125700000000000000)
      constant := (109385192111997926417951153400205896217242901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44655977410427854221/25000000000000000000)
  centralHi := (35724781928342283377/20000000000000000000)
  directionLo := (185366791345754018241/100000000000000000000)
  directionHi := (92683395672877009121/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree015.table
  base := (-1439417887554765249175689917080593099997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-10173906973334622345084277122400000000000000)
      constant := (47105625504037969317193692250207465000406348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree015.table
  base := (-2882669901335862897539826522114680447507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-26420720755261157475790589883400000000000000)
      constant := (122824015362650942854670675204200004934725834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185366791345754018241/100000000000000000000)
  centralHi := (92683395672877009121/50000000000000000000)
  directionLo := (47968214457564454399/25000000000000000000)
  directionHi := (191872857830257817597/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree016.table
  base := (-6490470082963191390338557635856623148261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-10741721594501024223955454312300000000000000)
      constant := (52628913588517702717167235748231846354569931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree016.table
  base := (-12991417874824295419215177803025684321/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-5579255830414301234210228128220000000000000)
      constant := (27447684754935520338800376313965783816455100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47968214457564454399/25000000000000000000)
  centralHi := (191872857830257817597/100000000000000000000)
  directionLo := (99082717728774919061/50000000000000000000)
  directionHi := (198165435457549838123/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree017.table
  base := (-3568706369746721711199729710184093771263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-11309536215667426102826631502200000000000000)
      constant := (58518558130434717962819347303975228790003746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree017.table
  base := (-892622419718436761213426235253589420481/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-29371837548881854866311691398800000000000000)
      constant := (152606811416806358199437381685852688666892088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99082717728774919061/50000000000000000000)
  centralHi := (198165435457549838123/100000000000000000000)
  directionLo := (8170570217379971581/4000000000000000000)
  directionHi := (102132127717249644763/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree018.table
  base := (-3854406082522455155387888519191270162499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-11877350836833827981697808692100000000000000)
      constant := (64769103740459650741886051860695636168076058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree018.table
  base := (-7711232940972481122740182356732833141451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-30847395945692203561572242156500000000000000)
      constant := (168915376199020745910479875690432751429353581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8170570217379971581/4000000000000000000)
  centralHi := (102132127717249644763/50000000000000000000)
  directionLo := (105093092406613949691/50000000000000000000)
  directionHi := (210186184813227899383/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree019.table
  base := (-8211273923154963409424033184312906788667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-12445165458000229860568985882000000000000000)
      constant := (71377056075481231608124348913048472308795157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree019.table
  base := (-4106456304788865381603668707629037011457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-32322954342502552256832792914200000000000000)
      constant := (186155297760431103371416904421861696662630734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105093092406613949691/50000000000000000000)
  centralHi := (210186184813227899383/100000000000000000000)
  directionLo := (21594577681554788017/10000000000000000000)
  directionHi := (215945776815547880171/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree020.table
  base := (-2162257685169314185579979165863615198421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-13012980079166631739440163071900000000000000)
      constant := (78340176022993877582851099083032590240141164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree020.table
  base := (-4325068708794074063368352704228445676651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-33798512739312900952093343671900000000000000)
      constant := (204320937116077335478953968129822515737329562) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21594577681554788017/10000000000000000000)
  centralHi := (215945776815547880171/100000000000000000000)
  directionLo := (110777846118482144683/50000000000000000000)
  directionHi := (221555692236964289367/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree021.table
  base := (-4512397980011424118137308376573571378449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-13580794700333033618311340261800000000000000)
      constant := (85657028224862139022783183242935161481600958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree021.table
  base := (-282048181466682415219637245763097121801/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-35274071136123249647353894429600000000000000)
      constant := (223408687714957129756195622346360241288141792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110777846118482144683/50000000000000000000)
  centralHi := (221555692236964289367/100000000000000000000)
  directionLo := (227027027027027027027/100000000000000000000)
  directionHi := (56756756756756756757/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree022.table
  base := (-4670154825042556744701978816311663073369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-14148609321499435497182517451700000000000000)
      constant := (93326692184641420236517330401942260468375598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree022.table
  base := (-9340811398440113788754785339200942643781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-36749629532933598342614445187300000000000000)
      constant := (243416241942160629222485367138233909520663811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227027027027027027027/100000000000000000000)
  centralHi := (56756756756756756757/25000000000000000000)
  directionLo := (116184785190295551563/50000000000000000000)
  directionHi := (232369570380591103127/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree023.table
  base := (-959668818404777596400735657878927638959/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 46000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (90)
      square := (4367804778203091375932132230000000000000)
      linear := (-127968903849268151096119083840000000000000)
      constant := (881291976877543752282583902787569328607886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree023.table
  base := (-38388100704074336926396994981918719609/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-7645037585948789407574999189000000000000000)
      constant := (52868424533742568888571335735597663642763950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116184785190295551563/50000000000000000000)
  centralHi := (232369570380591103127/100000000000000000000)
  directionLo := (237592010549577411537/100000000000000000000)
  directionHi := (118796005274788705769/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree024.table
  base := (-9794648096797945804341522088614608671569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-15284238563832239254924871831500000000000000)
      constant := (109722304646735191584410839703922872012739999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree024.table
  base := (-9794874107523706566605585708532220554301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-39700746326554295733135546702700000000000000)
      constant := (286185383959621022482330589802619390061161931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237592010549577411537/100000000000000000000)
  centralHi := (118796005274788705769/50000000000000000000)
  directionLo := (121351050381857558451/50000000000000000000)
  directionHi := (242702100763715116903/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree025.table
  base := (-9934649490808799025247501994095771202159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-15852053184998641133796049021400000000000000)
      constant := (118447630707886090340407488748873337034057889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree025.table
  base := (-2483700219007773301118065648117456327359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-41176304723364644428396097460400000000000000)
      constant := (308945419781754649950660900059658809151382116) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121351050381857558451/50000000000000000000)
  centralHi := (242702100763715116903/100000000000000000000)
  directionLo := (247706794321937297653/100000000000000000000)
  directionHi := (123853397160968648827/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree026.table
  base := (-10016987939939984171574298430083989196063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-16419867806165043012667226211300000000000000)
      constant := (127524399165798473700261973826085569715282673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree026.table
  base := (-2003417844926927073067835599908360134221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-8530372624034998624731329643620000000000000)
      constant := (66524368338163637953495217652525454976251451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247706794321937297653/100000000000000000000)
  centralHi := (123853397160968648827/50000000000000000000)
  directionLo := (252612355579414542933/100000000000000000000)
  directionHi := (126306177789707271467/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree027.table
  base := (-10041853410975630822326921188637575438833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-16987682427331444891538403401200000000000000)
      constant := (136952509528043537116680644755560722592857343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree027.table
  base := (-313810034598612055481097993551860532717/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-44127421516985341818917198975800000000000000)
      constant := (357214400592030346950623681921830093782733664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252612355579414542933/100000000000000000000)
  centralHi := (126306177789707271467/50000000000000000000)
  directionLo := (257424451887365570967/100000000000000000000)
  directionHi := (32178056485920696371/12500000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree028.table
  base := (-5004684027460045326724017447121107095273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-17555497048497846770409580591100000000000000)
      constant := (146731897176739978553089831950945868693201166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree028.table
  base := (-10009413260566542283574969854110314462079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-45602979913795690514177749733500000000000000)
      constant := (382722936672475635044911893456522979501413849) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257424451887365570967/100000000000000000000)
  centralHi := (32178056485920696371/12500000000000000000)
  directionLo := (262148230334748995777/100000000000000000000)
  directionHi := (131074115167374497889/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree029.table
  base := (-2479902613939252100254138360296409829601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-18123311669664248649280757781000000000000000)
      constant := (156862520540960449944103789962162796800564284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree029.table
  base := (-4959820309306561956172046378241406762699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-47078538310606039209438300491200000000000000)
      constant := (409147347347856301608585573050725028283730138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262148230334748995777/100000000000000000000)
  centralHi := (131074115167374497889/50000000000000000000)
  directionLo := (266788382254120345157/100000000000000000000)
  directionHi := (133394191127060172579/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree030.table
  base := (-9772631196201981458713673350699060931901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-18691126290830650528151934970900000000000000)
      constant := (167344352862448400268465165829480196767024371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree030.table
  base := (-610790706724609446506455646747620676319/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-48554096707416387904698851248900000000000000)
      constant := (436487566733269809001238044879640116705908624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266788382254120345157/100000000000000000000)
  centralHi := (133394191127060172579/50000000000000000000)
  directionLo := (271349197794835312857/100000000000000000000)
  directionHi := (135674598897417656429/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree031.table
  base := (-2392115713483898125848444573123798071313/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-19258940911997052407023112160800000000000000)
      constant := (178177376907610801290117990591620043281101692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree031.table
  base := (-4784238127455551151740294879143896187933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-50029655104226736599959402006600000000000000)
      constant := (464743552489101890596453539802654012237439446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271349197794835312857/100000000000000000000)
  centralHi := (135674598897417656429/50000000000000000000)
  directionLo := (275834612371309702043/100000000000000000000)
  directionHi := (68958653092827425511/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree032.table
  base := (-9307126423908993154905464663915295635277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-19826755533163454285894289350700000000000000)
      constant := (189361581570118493802162356754388808608938467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree032.table
  base := (-9307135348465399790341965529959539428213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-51505213501037085295219952764300000000000000)
      constant := (493915277388817141928815538671085390522776403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275834612371309702043/100000000000000000000)
  centralHi := (68958653092827425511/25000000000000000000)
  directionLo := (35031030802204649897/12500000000000000000)
  directionHi := (280248246417637199177/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree033.table
  base := (-2247158861578584057362132499369471242481/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-20394570154329856164765466540600000000000000)
      constant := (200896959687209828964828571423084198850910204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree033.table
  base := (-2247160346697042747641103933710022075583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-52980771897847433990480503522000000000000000)
      constant := (524002723911225902007058431124553919114107492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35031030802204649897/12500000000000000000)
  centralHi := (280248246417637199177/100000000000000000000)
  directionLo := (284593439591095850607/100000000000000000000)
  directionHi := (17787089974443490663/6250000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree034.table
  base := (-8612998661042895725151503022835905951217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-20962384775496258043636643730500000000000000)
      constant := (212783506635482322833106642899719805751806207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree034.table
  base := (-1722600522696699799645511772021074018763/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-10891266058931556537148210855940000000000000)
      constant := (111001176154166836215077443890823149668313453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284593439591095850607/100000000000000000000)
  centralHi := (17787089974443490663/6250000000000000000)
  directionLo := (72218320085877770069/25000000000000000000)
  directionHi := (288873280343511080277/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree035.table
  base := (-2045055428846286716589246006769046396389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-21530199396662659922507820920400000000000000)
      constant := (225021219427519314013319335632426697825240876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree035.table
  base := (-2045056086023703042935713022269128008643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-55931888691468131381001605037400000000000000)
      constant := (586924740690663025711136618775804255024670932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72218320085877770069/25000000000000000000)
  centralHi := (288873280343511080277/100000000000000000000)
  directionLo := (293090631604885602121/100000000000000000000)
  directionHi := (146545315802442801061/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree036.table
  base := (-3845154131577305785593483875443115138207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-22098014017829061801378998110300000000000000)
      constant := (237610096130453449410780114403381184183776994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree036.table
  base := (-3845155005441478030342573412282375976167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-57407447088278480076262155795100000000000000)
      constant := (619759298971947338356938657519170854577254754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293090631604885602121/100000000000000000000)
  centralHi := (146545315802442801061/50000000000000000000)
  directionLo := (4644502393536324331/1562500000000000000)
  directionHi := (59449630637264951437/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree037.table
  base := (-7143260672444833131569497455999983993827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-22665828638995463680250175300200000000000000)
      constant := (250550135491563244624059044327126008467265517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree037.table
  base := (-3571630917051522590960439517765971791037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (720)
      square := (35132342781198778458584541850000000000000)
      linear := (-1591432580678076453284397474400000000000000)
      constant := (17662420339869131547005491482235318087463262) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4644502393536324331/1562500000000000000)
  centralHi := (59449630637264951437/20000000000000000000)
  directionLo := (75337080350088399717/25000000000000000000)
  directionHi := (301348321400353598869/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree038.table
  base := (-1307816096318112847077788367048776090353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-4646728652032373111824270498020000000000000)
      constant := (52768267339413923096253058873031197448203263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree038.table
  base := (-3269540626756151451472687665497504625451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-60358563881899177466783257310500000000000000)
      constant := (688175499529266973567829098618667832335515162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75337080350088399717/25000000000000000000)
  centralHi := (301348321400353598869/100000000000000000000)
  directionLo := (305393446309741284737/100000000000000000000)
  directionHi := (152696723154870642369/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree039.table
  base := (-5877768693056067729659892510267658914953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-23801457881328267437992529680000000000000000)
      constant := (277483699216668966936328145549618408433989863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree039.table
  base := (-1469442301471802788569585533326020220319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-61834122278709526162043808068200000000000000)
      constant := (723757138551827653579934920754856713273533156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (305393446309741284737/100000000000000000000)
  centralHi := (152696723154870642369/50000000000000000000)
  directionLo := (151067229954119349/48828125000000000)
  directionHi := (309385686946036426753/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree040.table
  base := (-644915745369289114165417932270109174363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-24369272502494669316863706869900000000000000)
      constant := (291477222703277538230107812066632897974095784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree040.table
  base := (-5159326303594613652551282907043567668191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-63309680675519874857304358825900000000000000)
      constant := (760254468804509698227452123008257355862246521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151067229954119349/48828125000000000)
  centralHi := (309385686946036426753/100000000000000000000)
  directionLo := (313327064782474347539/100000000000000000000)
  directionHi := (15666353239123717377/5000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree041.table
  base := (-4383752723324974292880654614671700531183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-24937087123661071195734884059800000000000000)
      constant := (305821906928346341548665074510188670419004193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree041.table
  base := (-547969118694434760540843172906251486189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-64785239072330223552564909583600000000000000)
      constant := (797667489735714302747476577535080733723258072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313327064782474347539/100000000000000000000)
  centralHi := (15666353239123717377/5000000000000000000)
  directionLo := (317219475699918050391/100000000000000000000)
  directionHi := (39652434462489756299/12500000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree042.table
  base := (-1775524630535502752770862746331578908309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-25504901744827473074606061249700000000000000)
      constant := (320517751740103714417915896037981189515009078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree042.table
  base := (-710209882259848684625082836199633902027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-13252159493828114449565092068260000000000000)
      constant := (167199240195838733037051693418362701188125037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317219475699918050391/100000000000000000000)
  centralHi := (39652434462489756299/12500000000000000000)
  directionLo := (32106470064686482189/10000000000000000000)
  directionHi := (321064700646864821891/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree043.table
  base := (-2661215768945467271721872423920196354979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-26072716365993874953477238439600000000000000)
      constant := (335564757036583287716760574310496216128216109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree043.table
  base := (-2661215868694324988747887895713811533297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-67736355865950920943086011099000000000000000)
      constant := (875240602288707924967990772201317792010916407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32106470064686482189/10000000000000000000)
  centralHi := (321064700646864821891/100000000000000000000)
  directionLo := (81216103790901185371/25000000000000000000)
  directionHi := (64972883032720948297/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree044.table
  base := (-857126189252787684465180392284657028961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-26640530987160276832348415629500000000000000)
      constant := (350962922748191294298896707943762832863359262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree044.table
  base := (-342850488946356800611293605552507229783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-13842382852552253927669312371340000000000000)
      constant := (183080138699176463856588800421918617602427073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81216103790901185371/25000000000000000000)
  centralHi := (64972883032720948297/20000000000000000000)
  directionLo := (328620197915041375819/100000000000000000000)
  directionHi := (16431009895752068791/5000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree045.table
  base := (-710159181426514785783824928366782079569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-27208345608326678711219592819400000000000000)
      constant := (366712248826431561305346097364643972279907999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree045.table
  base := (-710159225393448948173880295552050290717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-70687472659571618333607112614400000000000000)
      constant := (956476474483007724938092145308139243152008427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (328620197915041375819/100000000000000000000)
  centralHi := (16431009895752068791/5000000000000000000)
  directionLo := (6646670767108928681/2000000000000000000)
  directionHi := (332333538355446434051/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree046.table
  base := (438829695877956861318854275631272543/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 46000000000000000000000000000000000000000
      center := (117)
      previous := (0)
      next := (90)
      square := (4367804778203091375932132230000000000000)
      linear := (-241531828082548526870354521820000000000000)
      constant := (3328806393361802809748749563574323082958240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree046.table
  base := (175531863757171703152607927498732746947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-72163031056381967028867663372100000000000000)
      constant := (998467945165471266895860113015491530261140886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6646670767108928681/2000000000000000000)
  centralHi := (332333538355446434051/100000000000000000000)
  directionLo := (67201168726140770307/20000000000000000000)
  directionHi := (21000365226918990721/6250000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree047.table
  base := (73470819371950271816392111215328448137/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-5668794970131896493792389439840000000000000)
      constant := (79852876390618545999197851425001634996257892) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree047.table
  base := (1469416368062635631874306538479508261813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-73638589453192315724128214129800000000000000)
      constant := (1041375105480396202436622487722528446810421997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67201168726140770307/20000000000000000000)
  centralHi := (21000365226918990721/6250000000000000000)
  directionLo := (339638444808756934027/100000000000000000000)
  directionHi := (84909611202189233507/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree048.table
  base := (132244933684533137304112866025193202347/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-5782357894365176869566624877820000000000000)
      constant := (83213437791253144249606111718909308816166252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree048.table
  base := (1322449330413927635046078928436332882653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-75114147850002664419388764887500000000000000)
      constant := (1085197955379287660864773220222858679432703914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339638444808756934027/100000000000000000000)
  centralHi := (84909611202189233507/25000000000000000000)
  directionLo := (85808150629121856989/25000000000000000000)
  directionHi := (343232602516487427957/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree049.table
  base := (969377646486893497219536893031889322959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-29479604092992286226704301579000000000000000)
      constant := (433221156230515632023056248398205477807381244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree049.table
  base := (1938755288704352044552617448226763416163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-76589706246813013114649315645200000000000000)
      constant := (1129936494823264264900904821219594878233454294) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85808150629121856989/25000000000000000000)
  centralHi := (343232602516487427957/100000000000000000000)
  directionLo := (173394756025356108357/50000000000000000000)
  directionHi := (69357902410142443343/20000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree050.table
  base := (5167252099831705187123023275271867585473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-30047418714158688105575478768900000000000000)
      constant := (450726283762946482346919899482618817952715217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree050.table
  base := (322953255885197724194029723771367448379/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-78065264643623361809909866402900000000000000)
      constant := (1175590723779960091216040684729488032589293616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173394756025356108357/50000000000000000000)
  centralHi := (69357902410142443343/20000000000000000000)
  directionLo := (350310308022046498971/100000000000000000000)
  directionHi := (87577577005511624743/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree051.table
  base := (12722896864252671701591629931134650037/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-30615233335325089984446655958800000000000000)
      constant := (468582571542530903040362069767937957693221376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree051.table
  base := (3257061595367102327408615931236431788237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-79540823040433710505170417160600000000000000)
      constant := (1222160642221506366959586555577475350236192906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350310308022046498971/100000000000000000000)
  centralHi := (87577577005511624743/25000000000000000000)
  directionLo := (353796068582779926859/100000000000000000000)
  directionHi := (17689803429138996343/5000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree052.table
  base := (3959061925792044002876380598318097789927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-31183047956491491863317833148700000000000000)
      constant := (486790019559556203275175598448620547461742766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree052.table
  base := (1979530962271439946096636246058000271087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-81016381437244059200430967918300000000000000)
      constant := (1269646250123211715713286257223013609484472412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353796068582779926859/100000000000000000000)
  centralHi := (17689803429138996343/5000000000000000000)
  directionLo := (357247819283422833769/100000000000000000000)
  directionHi := (35724781928342283377/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree053.table
  base := (73275422300998715674153508835871883563/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-31750862577657893742189010338600000000000000)
      constant := (505348627805260011253069125934044556979817856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree053.table
  base := (4689627026434574989177185843179026489961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-82491939834054407895691518676000000000000000)
      constant := (1318047547462694795929619728444174174529513218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357247819283422833769/100000000000000000000)
  centralHi := (35724781928342283377/10000000000000000000)
  directionLo := (360666536597022210393/100000000000000000000)
  directionHi := (180333268298511105197/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree054.table
  base := (2179502757621014515965929116490755890191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-6463735439764859124212037505700000000000000)
      constant := (104851679254317815060336925960383609865911039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree054.table
  base := (10897513787003787362777498831287575740073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-83967498230864756590952069433700000000000000)
      constant := (1367364534219310282809158710455632691188159937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360666536597022210393/100000000000000000000)
  centralHi := (180333268298511105197/50000000000000000000)
  directionLo := (182026575572786337677/50000000000000000000)
  directionHi := (72810630229114535071/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree055.table
  base := (2494580607625656097873495902900111087249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-6577298363998139499986272943680000000000000)
      constant := (108703864990207639633569899134784158765154721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree055.table
  base := (12472903037397041659381936870536973024917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-85443056627675105286212620191400000000000000)
      constant := (1417597210373765365500946111565515116071111373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182026575572786337677/50000000000000000000)
  centralHi := (72810630229114535071/20000000000000000000)
  directionLo := (14696342026349343521/4000000000000000000)
  directionHi := (183704275329366794013/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree056.table
  base := (1763177723905029883059890646182788998479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-33454306441157099378802541908300000000000000)
      constant := (563131413836541410328508355924245563041563128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree056.table
  base := (2821084358150935440240210210729273721211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-17383723004897090796294634189820000000000000)
      constant := (293749115181572047075380921760088375724337859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14696342026349343521/4000000000000000000)
  centralHi := (183704275329366794013/50000000000000000000)
  directionLo := (370733582691508036483/100000000000000000000)
  directionHi := (92683395672877009121/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree057.table
  base := (15795070034772846190103975752189671777507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-34022121062323501257673719098200000000000000)
      constant := (583094662921397285764794149558258336370301203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree057.table
  base := (15424873080517968490591690181491250459/9765625000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-88394173421295802676733721706800000000000000)
      constant := (1520809630804309495603487608741414598403451904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370733582691508036483/100000000000000000000)
  centralHi := (92683395672877009121/25000000000000000000)
  directionLo := (18701452856222912253/5000000000000000000)
  directionHi := (374029057124458245061/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree058.table
  base := (8770923878324133808617624878241247906437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-34589935683489903136544896288100000000000000)
      constant := (603409072199216650158982289159179240285010346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree058.table
  base := (3508369551286825320284249319879870171227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-17973946363621230274398854492900000000000000)
      constant := (314757875009323316604527785958275542264409763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18701452856222912253/5000000000000000000)
  centralHi := (374029057124458245061/100000000000000000000)
  directionLo := (188647874233677273499/50000000000000000000)
  directionHi := (377295748467354546999/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree059.table
  base := (19345754945307979976344901805520610529013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-35157750304656305015416073478000000000000000)
      constant := (624074641663885044648592438722670402969847877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree059.table
  base := (9672877472582878048550241678297826538063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-91345290214916500067254823222200000000000000)
      constant := (1627684808618983098399848548282529449061216494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188647874233677273499/50000000000000000000)
  centralHi := (377295748467354546999/100000000000000000000)
  directionLo := (190267198992411256941/50000000000000000000)
  directionHi := (380534397984822513883/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree060.table
  base := (848271663586412506702178352889801030187/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-7145112985164541378857450133580000000000000)
      constant := (129018274261906995097257777198193523724844615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree060.table
  base := (2650848948695730806543676594146354084557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-92820848611726848762515373979900000000000000)
      constant := (1682495931506241285953281280481090869934068264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190267198992411256941/50000000000000000000)
  centralHi := (380534397984822513883/100000000000000000000)
  directionLo := (383745715660515635193/100000000000000000000)
  directionHi := (191872857830257817597/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree061.table
  base := (23124957679040365643129991958184528989427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-36293379546989108773158427857800000000000000)
      constant := (666459261130524710546820382603229615835406883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree061.table
  base := (23124957678977615818441268961988510664869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-94296407008537197457775924737600000000000000)
      constant := (1738222743693802011332030183969712271100205661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383745715660515635193/100000000000000000000)
  centralHi := (191872857830257817597/50000000000000000000)
  directionLo := (386930382014557415579/100000000000000000000)
  directionHi := (19346519100727870779/5000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree062.table
  base := (25100253203178304113893175866768461336557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-36861194168155510652029605047700000000000000)
      constant := (688178311121421507226711594451120516047038653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree062.table
  base := (25100253203136619002555046364648469121803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-95771965405347546153036475495300000000000000)
      constant := (1794865245167613249067123302056803754227748307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386930382014557415579/100000000000000000000)
  centralHi := (19346519100727870779/5000000000000000000)
  directionLo := (24380565611714480531/6250000000000000000)
  directionHi := (390089049787431688497/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree063.table
  base := (27132678152173411264258871343643594251143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-37429008789321912530900782237600000000000000)
      constant := (710248521276987886330517982895537461358854647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree063.table
  base := (3391584769018214686661807602898699346057/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-97247523802157894848297026253000000000000000)
      constant := (1852423435914125816536459121757496555238016264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24380565611714480531/6250000000000000000)
  centralHi := (390089049787431688497/100000000000000000000)
  directionLo := (78644469100424698733/20000000000000000000)
  directionHi := (196611172751061746833/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree064.table
  base := (7305558129118044376669540353355364428311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-37996823410488314409771959427500000000000000)
      constant := (732669891592170041286426170856499951130306076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree064.table
  base := (7305558129113444396487353102862181124797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-98723082198968243543557577010700000000000000)
      constant := (1910897315920264211698289516272873303839388372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78644469100424698733/20000000000000000000)
  centralHi := (196611172751061746833/50000000000000000000)
  directionLo := (79266174183019935249/20000000000000000000)
  directionHi := (198165435457549838123/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree065.table
  base := (31368916286849289025097857422874060735479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-38564638031654716288643136617400000000000000)
      constant := (755442422062087781085744021536450378129068391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree065.table
  base := (7842229071709265770246109889121319305261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-100198640595778592238818127768400000000000000)
      constant := (1970286885173401139695450438709578344515609236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79266174183019935249/20000000000000000000)
  centralHi := (198165435457549838123/50000000000000000000)
  directionLo := (199707602182823416171/50000000000000000000)
  directionHi := (399415204365646832343/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree066.table
  base := (33572729454390759171089863728635612996877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-39132452652821118167514313807300000000000000)
      constant := (778566112682025606791453072340048239275347933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree066.table
  base := (16786364727191317480200336150564912014289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-101674198992588940934078678526100000000000000)
      constant := (2030592143661334787012301436096246729095123282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199707602182823416171/50000000000000000000)
  centralHi := (399415204365646832343/100000000000000000000)
  directionLo := (100618975508033972401/25000000000000000000)
  directionHi := (80495180406427177921/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree067.table
  base := (35833672010478694924982368172693687490873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-39700267273987520046385490997200000000000000)
      constant := (802040963447424652996146934635704960682671817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree067.table
  base := (8958418002618323985848016021783909268771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-103149757389399289629339229283800000000000000)
      constant := (2091813091372268210571419030694638687155789996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100618975508033972401/25000000000000000000)
  centralHi := (80495180406427177921/20000000000000000000)
  directionLo := (405513499102941662139/100000000000000000000)
  directionHi := (20275674955147083107/5000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree068.table
  base := (38151743946777353350451882871621264071693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-40268081895153921925256668187100000000000000)
      constant := (825866974353875311686510483333087648693925597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree068.table
  base := (19075871973386882586676991112814098742719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-104625315786209638324599780041500000000000000)
      constant := (2153949728294790410880111480353685002357564622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405513499102941662139/100000000000000000000)
  centralHi := (20275674955147083107/5000000000000000000)
  directionLo := (8170570217379971581/2000000000000000000)
  directionHi := (408528510868998579051/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree069.table
  base := (10131736313805062443173617830176672513237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 230000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (450)
      square := (21839023891015456879660661150000000000000)
      linear := (-1775473761579144513222949799000000000000000)
      constant := (36958441104222191846503149392226253871217804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree069.table
  base := (5065868156902233111543382374143579042837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-106100874183019987019860330799200000000000000)
      constant := (2217002054417858790587759790659970477677150824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8170570217379971581/2000000000000000000)
  centralHi := (408528510868998579051/100000000000000000000)
  directionLo := (411521433744308769087/100000000000000000000)
  directionHi := (6430022402254824517/1562500000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree070.table
  base := (21479637963999074898477316717560259638419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-41403711137486725682999022566900000000000000)
      constant := (874572476572998870350507133155178754697447302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree070.table
  base := (21479637963998282288972595349893932210291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-107576432579830335715120881556900000000000000)
      constant := (2280970069730782786909162625662009586391776758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411521433744308769087/100000000000000000000)
  centralHi := (6430022402254824517/1562500000000000000)
  directionLo := (10362318655503142687/2500000000000000000)
  directionHi := (414492746220125707481/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree071.table
  base := (22724367978773911964399772484957465010677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-41971525758653127561870199756800000000000000)
      constant := (899451967877539736926759610709434997981296266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree071.table
  base := (1817949438301870806814394729547738055189/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-21810398195328136882076286462920000000000000)
      constant := (469170754844641704815293903278504266987768705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10362318655503142687/2500000000000000000)
  centralHi := (414492746220125707481/100000000000000000000)
  directionLo := (417442909758006976117/100000000000000000000)
  directionHi := (208721454879003488059/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree072.table
  base := (47995325336541474700724385230564345314381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-42539340379819529440741376946700000000000000)
      constant := (924682619306856607338019818536568538671307549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree072.table
  base := (5999415667067596772483530915789948780561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-110527549373451033105641983072300000000000000)
      constant := (2411653167885104370536249889027331519044704072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417442909758006976117/100000000000000000000)
  centralHi := (208721454879003488059/50000000000000000000)
  directionLo := (84074473925291159753/20000000000000000000)
  directionHi := (210186184813227899383/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree073.table
  base := (25299522028938383606523351775319346404689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-43107155000985931319612554136600000000000000)
      constant := (950264430857192346422355740234037868496160962) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree073.table
  base := (25299522028938150744688075315540446988027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-112003107770261381800902533830000000000000000)
      constant := (2478368250706747311653201814799499743853217926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84074473925291159753/20000000000000000000)
  centralHi := (210186184813227899383/50000000000000000000)
  directionLo := (423281555685446326899/100000000000000000000)
  directionHi := (4232815556854463269/1000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree074.table
  base := (53259892114667408351257272297292219892719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-43674969622152333198483731326500000000000000)
      constant := (976197402524904105122191994384067584323248351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree074.table
  base := (26629946057333549353950418390454157124043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 370000000000000000000000000000000000000000
      center := (945)
      previous := (0)
      next := (720)
      square := (35132342781198778458584541850000000000000)
      linear := (-3066990977488425148544948232100000000000000)
      constant := (68810784396721893690137024885693607627179182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423281555685446326899/100000000000000000000)
  centralHi := (4232815556854463269/1000000000000000000)
  directionLo := (213085441561373228897/50000000000000000000)
  directionHi := (85234176624549291559/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree075.table
  base := (27988934750117114960681837427908764483883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-44242784243318735077354908516400000000000000)
      constant := (1002481534306458603462906592597477472823948214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree075.table
  base := (1749308421882313251200700316279209572359/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-114954224563882079191423635345400000000000000)
      constant := (2614545483791848890061733969789309612945903072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213085441561373228897/50000000000000000000)
  centralHi := (85234176624549291559/20000000000000000000)
  directionLo := (214520376572804642473/50000000000000000000)
  directionHi := (429040753145609284947/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree076.table
  base := (2350119048323869521300051136204375350567/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-8962119772897027391245217141260000000000000)
      constant := (205823365239685532035246428822380572802249715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree076.table
  base := (58752976208096601132643339823125715931301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-116429782960692427886684186103100000000000000)
      constant := (2684007634037292010112374642151859105109951069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214520376572804642473/50000000000000000000)
  centralHi := (429040753145609284947/100000000000000000000)
  directionLo := (431891553631095760341/100000000000000000000)
  directionHi := (215945776815547880171/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree077.table
  base := (3079260611598254811030446592344721781383/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-9075682697130307767019452579240000000000000)
      constant := (211220655639496790354536059999271431289406428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree077.table
  base := (15396303057991251296395207623169594994357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-117905341357502776581944736860800000000000000)
      constant := (2754385473406428656528970490962826702189098932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (431891553631095760341/100000000000000000000)
  centralHi := (215945776815547880171/50000000000000000000)
  directionLo := (27170228733625811229/6250000000000000000)
  directionHi := (86944731947602595933/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree078.table
  base := (32237288782866256840772934935831419723039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-45946228106817940713968440086100000000000000)
      constant := (1083440890300396985916860595402109642066975262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree078.table
  base := (32237288782866226571233773746637479176583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-119380899754313125277205287618500000000000000)
      constant := (2825679001890898643309545035105093417985484254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27170228733625811229/6250000000000000000)
  centralHi := (86944731947602595933/20000000000000000000)
  directionLo := (109384358620800336207/25000000000000000000)
  directionHi := (437537434483201344829/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree079.table
  base := (67421072203468012981625147488060073043047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-46514042727984342592839617276000000000000000)
      constant := (1111129662504029275546352636428733778639771863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree079.table
  base := (269684288813871890882839001339150090989/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-24171291630224694794493167675240000000000000)
      constant := (579577643896516493879845488769534823728197050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109384358620800336207/25000000000000000000)
  centralHi := (437537434483201344829/100000000000000000000)
  directionLo := (440333229284676778401/100000000000000000000)
  directionHi := (220166614642338389201/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree080.table
  base := (14084939227881910802165465427919740747461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-9416371469830148894342158893180000000000000)
      constant := (227833918961066540288591228121769542855406869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree080.table
  base := (70424696139409527234508766568843362232957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-122332016547933822667726389133900000000000000)
      constant := (2971013126173591906575159334608746562896918133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440333229284676778401/100000000000000000000)
  centralHi := (220166614642338389201/50000000000000000000)
  directionLo := (443111384473928578733/100000000000000000000)
  directionHi := (221555692236964289367/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree081.table
  base := (36742724683978746459395510793837241955711/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-47649671970317146350581971655800000000000000)
      constant := (1167560687201345052009829934093229801989142238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree081.table
  base := (73485449367957475109924545845764825661567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-123807574944744171362986939891600000000000000)
      constant := (3045053721956261045522616778459602046330685223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443111384473928578733/100000000000000000000)
  centralHi := (221555692236964289367/50000000000000000000)
  directionLo := (13933507180608972993/3125000000000000000)
  directionHi := (445872229779487135777/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree082.table
  base := (76603331883668356445308834342864307159893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-48217486591483548229453148845700000000000000)
      constant := (1196302939689186729892324304138975218487583397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree082.table
  base := (19150832970917086150052501420851423555319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-125283133341554520058247490649300000000000000)
      constant := (3120010006823137773420303019482182395388926844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13933507180608972993/3125000000000000000)
  centralHi := (445872229779487135777/100000000000000000000)
  directionLo := (224308042391853282459/50000000000000000000)
  directionHi := (448616084783706564919/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree083.table
  base := (39889171840624456752562892650891031144657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-48785301212649950108324326035600000000000000)
      constant := (1225396352266057615846339366271392710951047106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree083.table
  base := (39889171840624452813191599876274242322411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-126758691738364868753508041407000000000000000)
      constant := (3195881980766975658290091773151788875478761318) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224308042391853282459/50000000000000000000)
  centralHi := (448616084783706564919/100000000000000000000)
  directionLo := (451343259354553581269/100000000000000000000)
  directionHi := (45134325935455358127/10000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree084.table
  base := (1037631059444381589563043355369086648597/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-9870623166763270397439100645100000000000000)
      constant := (250968184985846816186842632739603949393725008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree084.table
  base := (83010484755550521924337832287379428514071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-128234250135175217448768592164700000000000000)
      constant := (3272669643780726217086421520565022437635763199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451343259354553581269/100000000000000000000)
  centralHi := (45134325935455358127/10000000000000000000)
  directionLo := (227027027027027027027/50000000000000000000)
  directionHi := (90810810810810810811/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree085.table
  base := (86299755101563771296346155169361039207491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-49920930454982753866066680415400000000000000)
      constant := (1284636657676066138733855076012341989740762739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree085.table
  base := (86299755101563767810276299894628365465913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-129709808531985566144029142922400000000000000)
      constant := (3350372995857531546048173342676496232322834897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227027027027027027027/50000000000000000000)
  centralHi := (90810810810810810811/20000000000000000000)
  directionLo := (114187190131230313137/25000000000000000000)
  directionHi := (456748760524921252549/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree086.table
  base := (2801442334825415538214236069893700595481/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-50488745076149155744937857605300000000000000)
      constant := (1314783550503974729795566787124760563680302368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree086.table
  base := (8964615471441329490388778101153622849673/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-26237073385759182967857938736020000000000000)
      constant := (685798407398143458648540344953358619362404674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114187190131230313137/25000000000000000000)
  centralHi := (456748760524921252549/100000000000000000000)
  directionLo := (459427661856773579043/100000000000000000000)
  directionHi := (114856915464193394761/25000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree087.table
  base := (46524841794676468316268260884054016505023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-51056559697315557623809034795200000000000000)
      constant := (1345281603410449131082281705931679149462314334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree087.table
  base := (93049683589352935089896791451030415018489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-132660925325606263534550244437800000000000000)
      constant := (3508526767173785954520194528983810638160311441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459427661856773579043/100000000000000000000)
  centralHi := (114856915464193394761/25000000000000000000)
  directionLo := (231045516466621737873/50000000000000000000)
  directionHi := (462091032933243475747/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree088.table
  base := (12063792715220128486455683057520480965711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-51624374318481959502680211985100000000000000)
      constant := (1376130816393044483589749471575426675446888952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree088.table
  base := (96510341721761026865416273586878644362181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-134136483722416612229810795195500000000000000)
      constant := (3588977186400410475283199373437236864131825789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231045516466621737873/50000000000000000000)
  centralHi := (462091032933243475747/100000000000000000000)
  directionLo := (464739140761182206253/100000000000000000000)
  directionHi := (232369570380591103127/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree089.table
  base := (25007032276783988426187135813339669051229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-52192188939648361381551389175000000000000000)
      constant := (1407331189449379431768685583193576739712400564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree089.table
  base := (100028129107135953022043406360834896360957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-135612042119226960925071345953200000000000000)
      constant := (3670343294664428141573412796098332973118150133) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464739140761182206253/100000000000000000000)
  centralHi := (232369570380591103127/50000000000000000000)
  directionLo := (467372244783076469679/100000000000000000000)
  directionHi := (5842153059788455871/1250000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree090.table
  base := (103603045741091878809114209173326476621469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-52760003560814763260422566364900000000000000)
      constant := (1438882722577133868765105051378689706132757101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree090.table
  base := (10360304574109187835493227218955587572203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-27417520103207461924066379342180000000000000)
      constant := (750525018391966948999080147159100398772691814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467372244783076469679/100000000000000000000)
  centralHi := (5842153059788455871/1250000000000000000)
  directionLo := (469990597173711521309/100000000000000000000)
  directionHi := (46999059717371152131/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree091.table
  base := (3351096613104833658875967389633791479613/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-53327818181981165139293743554800000000000000)
      constant := (1470785415774046781861151489588070822166888864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree091.table
  base := (53617545809677338390936728884247354250139/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-138563158912847658315592447468600000000000000)
      constant := (3835822578280779006942618505714819255936880582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469990597173711521309/100000000000000000000)
  centralHi := (46999059717371152131/10000000000000000000)
  directionLo := (472594443122040945307/100000000000000000000)
  directionHi := (118148610780510236327/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree092.table
  base := (55462133368879019049732371257518149705999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 230000000000000000000000000000000000000000
      center := (585)
      previous := (0)
      next := (450)
      square := (21839023891015456879660661150000000000000)
      linear := (-2343288382745546392094126988900000000000000)
      constant := (65349533436431051862579864751045834886475954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree092.table
  base := (110924266737758037898443153133966757229181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-140038717309658007010852998226300000000000000)
      constant := (3919935753621557248471409910016000490646748789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472594443122040945307/100000000000000000000)
  centralHi := (118148610780510236327/25000000000000000000)
  directionLo := (237592010549577411537/50000000000000000000)
  directionHi := (19007360843966192923/4000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree093.table
  base := (114670571092239743728317867058054640429621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-54463447424313968897036097934600000000000000)
      constant := (1535644282366587188310426567001460904787269509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree093.table
  base := (7166910693264983974661202922775905674561/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-141514275706468355706113548984000000000000000)
      constant := (4004964617976608292989099918026033437895584144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237592010549577411537/50000000000000000000)
  centralHi := (19007360843966192923/4000000000000000000)
  directionLo := (238879781556587600409/50000000000000000000)
  directionHi := (477759563113175200819/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree094.table
  base := (59237002339419053002989862279953300127129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-55031262045480370775907275124500000000000000)
      constant := (1568600455757970035341141512440990591534502482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree094.table
  base := (118474004678838105917003327455000643884697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-142989834103278704401374099741700000000000000)
      constant := (4090909171340508589687650384805495881478150193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238879781556587600409/50000000000000000000)
  centralHi := (477759563113175200819/100000000000000000000)
  directionLo := (120080323737962493651/25000000000000000000)
  directionHi := (96064258990369994921/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree095.table
  base := (7645910468355534871439106330429958360027/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-55599076666646772654778452314400000000000000)
      constant := (1601907789210018377994076104927509167559268528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree095.table
  base := (122334567493688557883829246978655861468497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-144465392500089053096634650499400000000000000)
      constant := (4177769413707967546368859173431529874350372393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120080323737962493651/25000000000000000000)
  centralHi := (96064258990369994921/20000000000000000000)
  directionLo := (96573887282712624959/20000000000000000000)
  directionHi := (120717359103390781199/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree096.table
  base := (126252259533020389484642879538055963452283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-56166891287813174533649629504300000000000000)
      constant := (1635566282720737510650234310997231604666257707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree096.table
  base := (25250451906604077889051798757362724772757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-29188190179379880358379040251420000000000000)
      constant := (853109069014764612194910561218829570213904333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96573887282712624959/20000000000000000000)
  centralHi := (120717359103390781199/25000000000000000000)
  directionLo := (97080840305486046761/20000000000000000000)
  directionHi := (242702100763715116903/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree097.table
  base := (130227080793153621266176573926291838467483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5290000000000000000000000000000000000000000
      center := (13455)
      previous := (0)
      next := (10350)
      square := (502297549493355508232195206450000000000000)
      linear := (-56734705908979576412520806694200000000000000)
      constant := (1669575936288180724225713802080358382549298507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree097.table
  base := (130227080793153621239974085404456824443407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13690000000000000000000000000000000000000000
      center := (34965)
      previous := (0)
      next := (26640)
      square := (1299896682904354802967628048450000000000000)
      linear := (-147416509293709750487155752014800000000000000)
      constant := (4354236965433037241759086280285051392663024183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell204.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97080840305486046761/20000000000000000000)
  centralHi := (242702100763715116903/50000000000000000000)
  directionLo := (243962899381551520799/50000000000000000000)
  directionHi := (487925798763103041599/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 13
  qDenominator := 23
  table := BinomialMassData.Q13_23.Degree098.table
  base := (26851806254099201848081866780091316160723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1058000000000000000000000000000000000000000
      center := (2691)
      previous := (0)
      next := (2070)
      square := (100459509898671101646439041290000000000000)
      linear := (-11460504106029195658278396776820000000000000)
      constant := (340787349982089544323907309367068306249022467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q13_23.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 21
  qDenominator := 37
  table := BinomialMassData.Q21_37.Degree098.table
  base := (13425903127049600922297654897755245263199/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2738000000000000000000000000000000000000000
      center := (6993)
      previous := (0)
      next := (5328)
      square := (259979336580870960593525609690000000000000)
      linear := (-29778413538104019836483260554500000000000000)
      constant := (888768854956138461324971474233413861530638862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21_37.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell204.Kernel098
