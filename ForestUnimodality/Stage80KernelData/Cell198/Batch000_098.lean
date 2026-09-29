import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell198.Parameters
import ForestUnimodality.BinomialMassData.Q49_89.Batch000_049
import ForestUnimodality.BinomialMassData.Q49_89.Batch050_099
import ForestUnimodality.BinomialMassData.Q99_179.Batch000_049
import ForestUnimodality.BinomialMassData.Q99_179.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree000.table
  base := (2590895327059479240737971441/100000000000000000000000000)
  polynomial :=
    { denominator := 890000000000000000000000000000000000000000
      center := (2891)
      previous := (0)
      next := (2360)
      square := (119637091522035630408726802200000000000000)
      linear := (-421403397648596421687372524300000000000000)
      constant := (23058968410829365242567945824900000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree000.table
  base := (2590895327059479240737971441/100000000000000000000000000)
  polynomial :=
    { denominator := 1790000000000000000000000000000000000000000
      center := (5841)
      previous := (0)
      next := (4720)
      square := (240618420027464919586090984200000000000000)
      linear := (-847541664933693926764490807300000000000000)
      constant := (46377026354364678409209688793900000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree001.table
  base := (80845454659189001301250071711284699866599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-49229337359884573310231381278300000000000000)
      constant := (1304629972192781557980583238640672215286661358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree001.table
  base := (161252437829711369752517844240094978792893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-199352405188569266968889869378300000000000000)
      constant := (5263770852004458946581523796639383215503084613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24858765878532948431/50000000000000000000)
  directionHi := (49717531757065896863/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree002.table
  base := (3214758651141083855436555577472546745041/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-60953772329044065090286607893900000000000000)
      constant := (869058889780107955144570518313721368559032352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree002.table
  base := (51173779769953478543226172287657373550957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-246994852354007321046935884249900000000000000)
      constant := (3499830871571995207872048590062259811892426474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24858765878532948431/50000000000000000000)
  centralHi := (49717531757065896863/100000000000000000000)
  directionLo := (8788900962319705701/12500000000000000000)
  directionHi := (70311207698557645609/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree003.table
  base := (13351725741117643354675088360297930601389/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-72678207298203556870341834509500000000000000)
      constant := (619789014405461511381435775679899541468011345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree003.table
  base := (8285204704191449532014859667194843254707/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-294637299519445375124981899121500000000000000)
      constant := (2494023625969464218214093353319019781792535896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8788900962319705701/12500000000000000000)
  centralHi := (70311207698557645609/100000000000000000000)
  directionLo := (1076416137876966119/1250000000000000000)
  directionHi := (86113291030157289521/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree004.table
  base := (8818613248674507000186320266341752088161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-84402642267363048650397061125100000000000000)
      constant := (483496451606929543649077811308065091451616405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree004.table
  base := (43701192536908881558835357081641882351421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-342279746684883429203027913993100000000000000)
      constant := (1946654276176700262488021386660487552421880261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1076416137876966119/1250000000000000000)
  centralHi := (86113291030157289521/100000000000000000000)
  directionLo := (3977402540565271749/4000000000000000000)
  directionHi := (49717531757065896863/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree005.table
  base := (920761661483743913754171393663565627699/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-96127077236522540430452287740700000000000000)
      constant := (417318957211718028207962322443191306784120928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree005.table
  base := (3644520901701533408826700648219585086941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-389922193850321483281073928864700000000000000)
      constant := (1683097544689560389151527458865329806165412648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3977402540565271749/4000000000000000000)
  centralHi := (49717531757065896863/50000000000000000000)
  directionLo := (27792945170575976389/25000000000000000000)
  directionHi := (111171780682303905557/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree006.table
  base := (1969968607137549040061000793114613385027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-107851512205682032210507514356300000000000000)
      constant := (396124280176666896765259955359608526227988670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree006.table
  base := (4865250055960269712428825392947406149353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-437564641015759537359119943736300000000000000)
      constant := (1601284857415391185212774056310711361725677892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27792945170575976389/25000000000000000000)
  centralHi := (111171780682303905557/100000000000000000000)
  directionLo := (3805705752357182261/3125000000000000000)
  directionHi := (121782584075429832353/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree007.table
  base := (12928391940915157222360759422543806414347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-119575947174841523990562740971900000000000000)
      constant := (405095294816738093468507447311069490608042587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree007.table
  base := (12743335782330863474213246534533952646833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-485207088181197591437165958607900000000000000)
      constant := (1641224062638534317804391773242102376757176153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/3125000000000000000)
  centralHi := (121782584075429832353/100000000000000000000)
  directionLo := (16442528103644064359/12500000000000000000)
  directionHi := (131540224829152514873/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree008.table
  base := (4020094200315581871921583123950029725587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-131300382144001015770617967587500000000000000)
      constant := (435437296015852426340326078962416370912749254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree008.table
  base := (3947536788427255469201643229734247849887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-532849535346635645515211973479500000000000000)
      constant := (1767410518254920948825413823696630070716458734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16442528103644064359/12500000000000000000)
  centralHi := (131540224829152514873/100000000000000000000)
  directionLo := (8788900962319705701/6250000000000000000)
  directionHi := (140622415397115291217/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree009.table
  base := (2185014390813709196770177087096534417749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-143024817113160507550673194203100000000000000)
      constant := (481882449109683954042730689513883298245979658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree009.table
  base := (4254278490303111004862297404411728912559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-580491982512073699593257988351100000000000000)
      constant := (1958635161177264485358565893442856206087302919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8788900962319705701/6250000000000000000)
  centralHi := (140622415397115291217/100000000000000000000)
  directionLo := (37288148817799422647/25000000000000000000)
  directionHi := (149152595271197690589/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree010.table
  base := (1514707491986940107969533010511303858381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-154749252082319999330728420818700000000000000)
      constant := (541236962604658269571874097863260037862235901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree010.table
  base := (710298145295499527442987459630438936459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-628134429677511753671304003222700000000000000)
      constant := (2202070241455308147355943363595037787926165638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37288148817799422647/25000000000000000000)
  centralHi := (149152595271197690589/100000000000000000000)
  directionLo := (157220639994081437583/100000000000000000000)
  directionHi := (9826289999630089849/6250000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree011.table
  base := (-387062790589056481395418042195098804317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-166473687051479491110783647434300000000000000)
      constant := (611533655256590777634527794849045244742010086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree011.table
  base := (-852071833012031084850509601528966743199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-675776876842949807749350018094300000000000000)
      constant := (2489830507094445398818045400802910376581160841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157220639994081437583/100000000000000000000)
  centralHi := (9826289999630089849/6250000000000000000)
  directionLo := (164894398340766614483/100000000000000000000)
  directionHi := (41223599585191653621/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree012.table
  base := (-1326266078706974763418759054077723239141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-178198122020638982890838874049900000000000000)
      constant := (691536362184955959053857304924900708445528278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree012.table
  base := (-339767459251328973385817818989165553191/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-723419324008387861827396032965900000000000000)
      constant := (2816968385736993673069929325617745172081657352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164894398340766614483/100000000000000000000)
  centralHi := (41223599585191653621/25000000000000000000)
  directionLo := (1076416137876966119/625000000000000000)
  directionHi := (172226582060314579041/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree013.table
  base := (-844200861651031099504770073672233566247/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-189922556989798474670894100665500000000000000)
      constant := (780449085691128358810190843277511189608787565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree013.table
  base := (-33413640106227113303340077249518613797/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-771061771173825915905442047837500000000000000)
      constant := (3180300966058051528713930925801866284202281344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1076416137876966119/625000000000000000)
  centralHi := (172226582060314579041/100000000000000000000)
  directionLo := (44814777509902584277/25000000000000000000)
  directionHi := (179259110039610337109/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree014.table
  base := (-5546116137720586018553861536491932247689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-201646991958957966450949327281100000000000000)
      constant := (877744492297174625310248798800047404666055431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree014.table
  base := (-5594279682105807812726694900640290315863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-818704218339263969983488062709100000000000000)
      constant := (3577720300455032514285340273887184457989433617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44814777509902584277/25000000000000000000)
  centralHi := (179259110039610337109/100000000000000000000)
  directionLo := (186025969950993626101/100000000000000000000)
  directionHi := (93012984975496813051/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree015.table
  base := (-1668343366954835356218245270683024411971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-213371426928117458231004553896700000000000000)
      constant := (983062130386960674800928424659179054531110836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree015.table
  base := (-41969506450265767366308878078470744837/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-866346665504702024061534077580700000000000000)
      constant := (4007785181143142166964210276293535018348429280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186025969950993626101/100000000000000000000)
  centralHi := (93012984975496813051/50000000000000000000)
  directionLo := (3851103450193091839/2000000000000000000)
  directionHi := (192555172509654591951/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree016.table
  base := (-7634906350910475259751729667576299115083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-225095861897276950011059780512300000000000000)
      constant := (1096147497815750444165983926703128134709427557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree016.table
  base := (-23972656962268751064996624865384779597/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-913989112670140078139580092452300000000000000)
      constant := (4469477337307754098477644855892226008618407360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3851103450193091839/2000000000000000000)
  centralHi := (192555172509654591951/100000000000000000000)
  directionLo := (198870127028263587451/100000000000000000000)
  directionHi := (49717531757065896863/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree017.table
  base := (-4227063954787923650315460790142693669523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-236820296866436441791115007127900000000000000)
      constant := (1216815139239573022108306614946659446887416634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree017.table
  base := (-8485846804034755426782169237895903680059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-961631559835578132217626107323900000000000000)
      constant := (4962054073491050412034033816456677350187229581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198870127028263587451/100000000000000000000)
  centralHi := (49717531757065896863/25000000000000000000)
  directionLo := (204990634879383090851/100000000000000000000)
  directionHi := (51247658719845772713/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree018.table
  base := (-914859898687018426590580470096608849463/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-248544731835595933571170233743500000000000000)
      constant := (1344925955220591918291487730931447613034035770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree018.table
  base := (-1147039171217755087585146063870772393069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1009274007001016186295672122195500000000000000)
      constant := (5484957792686102719022244150363932654029409368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204990634879383090851/100000000000000000000)
  centralHi := (51247658719845772713/25000000000000000000)
  directionLo := (8437344923826917473/4000000000000000000)
  directionHi := (105466811547836468413/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree019.table
  base := (-4865911942427842474844484815054213878247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-260269166804755425351225460359100000000000000)
      constant := (1480372978182172456067361444511011143740811026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree019.table
  base := (-2439011060102884056923534453976299665091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1056916454166454240373718137067100000000000000)
      constant := (6037759327634343346473259689319681529723277076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8437344923826917473/4000000000000000000)
  centralHi := (105466811547836468413/50000000000000000000)
  directionLo := (1354460604070777657/625000000000000000)
  directionHi := (216713696651324425121/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree020.table
  base := (-1276800374995341531633949620477404410127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-271993601773914917131280686974700000000000000)
      constant := (1623072242384189572476384514183587837339072264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree020.table
  base := (-10235560529595931357201393525897697354493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1104558901331892294451764151938700000000000000)
      constant := (6620121571336430574943585716410711879064689787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1354460604070777657/625000000000000000)
  centralHi := (216713696651324425121/100000000000000000000)
  directionLo := (222343561364607811113/100000000000000000000)
  directionHi := (111171780682303905557/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree021.table
  base := (-10604793476565490858137865932467549058583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-283718036743074408911335913590300000000000000)
      constant := (1772956758786055509071768156265424543906964057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree021.table
  base := (-2655814919442158237922638270316508648631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1152201348497330348529810166810300000000000000)
      constant := (7231775461402155975152256481231654985556856516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222343561364607811113/100000000000000000000)
  centralHi := (111171780682303905557/50000000000000000000)
  directionLo := (113917176321562648801/50000000000000000000)
  directionHi := (227834352643125297603/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree022.table
  base := (-10909826887949039290914001623898710657237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-295442471712233900691391140205900000000000000)
      constant := (1929972414495779158848858641835698312884025723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree022.table
  base := (-10925926199407053610418304605348930296103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1199843795662768402607856181681900000000000000)
      constant := (7872503615203148770006488439622614924382563777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113917176321562648801/50000000000000000000)
  centralHi := (227834352643125297603/100000000000000000000)
  directionLo := (9327835779714549091/4000000000000000000)
  directionHi := (58298973623215931819/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree023.table
  base := (-11135073097920938180180883309147903506091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-307166906681393392471446366821500000000000000)
      constant := (2094075090622140834067082626188539456328253189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree023.table
  base := (-696818205338549423733150769135826737363/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1247486242828206456685902196553500000000000000)
      constant := (8542128807851602711727916960594203608130433872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9327835779714549091/4000000000000000000)
  centralHi := (58298973623215931819/25000000000000000000)
  directionLo := (238436906061837849903/100000000000000000000)
  directionHi := (14902306628864865619/6250000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree024.table
  base := (-352659507421861842619978081036538690803/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-318891341650552884251501593437100000000000000)
      constant := (2265228571315343856146827970705106464964781984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree024.table
  base := (-11297294192853222367191652332441308734299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1295128689993644510763948211425100000000000000)
      constant := (9240505597012206436780259051565848026844325741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238436906061837849903/100000000000000000000)
  centralHi := (14902306628864865619/6250000000000000000)
  directionLo := (3805705752357182261/1562500000000000000)
  directionHi := (48713033630171932941/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree025.table
  base := (-2272738380436693684693748917792020188677/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-330615776619712376031556820052700000000000000)
      constant := (2443402981767444552871203478753347040427447415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree025.table
  base := (-5687138940094427152210684694514762956177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1342771137159082564841994226296700000000000000)
      constant := (9967514054552542382608499288848604960242265486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/1562500000000000000)
  centralHi := (48713033630171932941/20000000000000000000)
  directionLo := (124293829392664742157/50000000000000000000)
  directionHi := (49717531757065896863/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree026.table
  base := (-11373958270890015464371198535280331903479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-342340211588871867811612046668300000000000000)
      constant := (2628573591199238128301312188625044490992542841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree026.table
  base := (-11383139179938658137069998553540233179583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1390413584324520618920040241168300000000000000)
      constant := (10723054954861998345918452082121017388692981097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124293829392664742157/50000000000000000000)
  centralHi := (49717531757065896863/20000000000000000000)
  directionLo := (126755332298473991171/50000000000000000000)
  directionHi := (253510664596947982343/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree027.table
  base := (-11318494390925774138906001950365493549231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-354064646558031359591667273283900000000000000)
      constant := (2820719875925009367788415756154254925596541249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree027.table
  base := (-453057859972150325583616624898649237507/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1438056031489958672998086256039900000000000000)
      constant := (11507046003605443103832372837987659494525955325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126755332298473991171/50000000000000000000)
  centralHi := (253510664596947982343/100000000000000000000)
  directionLo := (258339873090471868561/100000000000000000000)
  directionHi := (129169936545235934281/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree028.table
  base := (-11199454334843061560192735151722567191609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-365789081527190851371722499899500000000000000)
      constant := (3019824773536071367479493985646005545275265111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree028.table
  base := (-11206333600612824261887279861685934058371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1485698478655396727076132270911500000000000000)
      constant := (12319418832904103742485366368910520986835734789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258339873090471868561/100000000000000000000)
  centralHi := (129169936545235934281/50000000000000000000)
  directionLo := (52616089931661005949/20000000000000000000)
  directionHi := (131540224829152514873/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree029.table
  base := (-5509315563887453710098727982598051094679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-377513516496350343151777726515100000000000000)
      constant := (3225874081480345399184483733061781674558095282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree029.table
  base := (-11024575268686461541834578704625321349523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1533340925820834781154178285783100000000000000)
      constant := (13160116576877543255858912243535200078639933557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52616089931661005949/20000000000000000000)
  centralHi := (131540224829152514873/50000000000000000000)
  directionLo := (26773710231574334981/10000000000000000000)
  directionHi := (267737102315743349811/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree030.table
  base := (-431100742870313768306045366821703066013/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-389237951465509834931832953130700000000000000)
      constant := (3438855967351900089060146986776132250352775675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree030.table
  base := (-10782648938789162415075481776067688915717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1580983372986272835232224300654700000000000000)
      constant := (14029091897022452041822567663914015179451511603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26773710231574334981/10000000000000000000)
  centralHi := (267737102315743349811/100000000000000000000)
  directionLo := (68078534117061120339/25000000000000000000)
  directionHi := (272314136468244481357/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree031.table
  base := (-5238680973502660450091966885901226284697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-400962386434669326711888179746300000000000000)
      constant := (3658760567286164707754675217713052773197830126) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree031.table
  base := (-1310223154455279192050456389214371599197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1628625820151710889310270315526300000000000000)
      constant := (14926305362892134713850088904696958556721031384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68078534117061120339/25000000000000000000)
  centralHi := (272314136468244481357/100000000000000000000)
  directionLo := (27681550152486138351/10000000000000000000)
  directionHi := (276815501524861383511/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree032.table
  base := (-316224993963364167522048553941152171837/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-412686821403828818491943406361900000000000000)
      constant := (3885579654902368243317960700433028276700131936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree032.table
  base := (-5061504812253026540283641934114095902841/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1676268267317148943388316330397900000000000000)
      constant := (15851724117554183494844368980979700506354143038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27681550152486138351/10000000000000000000)
  centralHi := (276815501524861383511/100000000000000000000)
  directionLo := (281244830794230582433/100000000000000000000)
  directionHi := (140622415397115291217/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree033.table
  base := (-9703898558694338732132340205850531295143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-424411256372988310271998632977500000000000000)
      constant := (4119306367386944808880963056904757941611172297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree033.table
  base := (-4853588429531776025877414839896054450507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1723910714482586997466362345269500000000000000)
      constant := (16805320773845843592500205777841081038702610426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281244830794230582433/100000000000000000000)
  centralHi := (140622415397115291217/50000000000000000000)
  directionLo := (285605475809708954661/100000000000000000000)
  directionHi := (142802737904854477331/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree034.table
  base := (-9232181152185304093616200857837268756243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-436135691342147802052053859593100000000000000)
      constant := (4359934978256271802049720026657670994181799197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree034.table
  base := (-9234999543460998607623774356892376468873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1771553161648025051544408360141100000000000000)
      constant := (17787072499217664428778095792491411365560840207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285605475809708954661/100000000000000000000)
  centralHi := (142802737904854477331/50000000000000000000)
  directionLo := (1449502680029473961/500000000000000000)
  directionHi := (289900536005894792201/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree035.table
  base := (-1740930184527420633167267897744726476767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-447860126311307293832109086208700000000000000)
      constant := (4607460708491148380802731636339320107887642965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree035.table
  base := (-4353535928098737479184826856134368539953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1819195608813463105622454375012700000000000000)
      constant := (18796960255596356910581163861954697395222731854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1449502680029473961/500000000000000000)
  centralHi := (289900536005894792201/100000000000000000000)
  directionLo := (294132884493590683589/100000000000000000000)
  directionHi := (29413288449359068359/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree036.table
  base := (-126903303666661638464353518158640374497/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-459584561280466785612164312824300000000000000)
      constant := (4861879569356246385940712077096586213990992832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree036.table
  base := (-8123889280001611921538239208848784665993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1866838055978901159700500389884300000000000000)
      constant := (19834968167219812977884425922787276090516918287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294132884493590683589/100000000000000000000)
  centralHi := (29413288449359068359/10000000000000000000)
  directionLo := (298305190542395381177/100000000000000000000)
  directionHi := (149152595271197690589/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree037.table
  base := (-3742041505997395861060500471662564291483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-471308996249626277392219539439900000000000000)
      constant := (5123188231467365736377525581910021656494326314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree037.table
  base := (-1497173004896310313622671200155103976207/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1914480503144339213778546404755900000000000000)
      constant := (20901082994438978150591489233225251567491757565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298305190542395381177/100000000000000000000)
  centralHi := (149152595271197690589/50000000000000000000)
  directionLo := (75604984817698061759/25000000000000000000)
  directionHi := (302419939270792247037/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree038.table
  base := (-6791816515925330418247284008115457955837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-483033431218785769172274766055500000000000000)
      constant := (5391383915652126266790566714929517457531815123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree038.table
  base := (-849167963039725871591874532748611739329/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-1962122950309777267856592419627500000000000000)
      constant := (21995293695454874109277813804023413850081276088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75604984817698061759/25000000000000000000)
  centralHi := (302419939270792247037/100000000000000000000)
  directionLo := (61295889791262358899/20000000000000000000)
  directionHi := (4788741389942371789/1562500000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree039.table
  base := (-3022652417843618319078564616196420017447/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-494757866187945260952329992671100000000000000)
      constant := (5666464301934942884454714949883316314083604626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree039.table
  base := (-6046612736534769871232178368757322459503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2009765397475215321934638434499100000000000000)
      constant := (23117591061138622318335702057387746631075064377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61295889791262358899/20000000000000000000)
  centralHi := (4788741389942371789/1562500000000000000)
  directionLo := (310485886308185323713/100000000000000000000)
  directionHi := (155242943154092661857/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree040.table
  base := (-655599059213787305493534473236729623587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-506482301157104752732385219286700000000000000)
      constant := (5948427453612069238130094094807934917212538984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree040.table
  base := (-2622955920032536325311257036422652861749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2057407844640653376012684449370700000000000000)
      constant := (24267967410655902303452722695179963559313400582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310485886308185323713/100000000000000000000)
  centralHi := (155242943154092661857/50000000000000000000)
  directionLo := (157220639994081437583/50000000000000000000)
  directionHi := (314441279988162875167/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree041.table
  base := (-175619341739427294129831982143757324321/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-518206736126264244512440445902300000000000000)
      constant := (6237271753900541797830595923618482455851333975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree041.table
  base := (-4391440955251076924063014252804368323067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2105050291806091430090730464242300000000000000)
      constant := (25446416337718204456181711931840395234560610253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157220639994081437583/50000000000000000000)
  centralHi := (314441279988162875167/100000000000000000000)
  directionLo := (12733901304760240341/4000000000000000000)
  directionHi := (159173766309503004263/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree042.table
  base := (-3482548443958343087603560128899898582337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-529931171095423736292495672517900000000000000)
      constant := (6532995853070317577206792314475583903329308623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree042.table
  base := (-3483366847066658473842022180724021921867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2152692738971529484168776479113900000000000000)
      constant := (26652932499009000822582368960588021613601459453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12733901304760240341/4000000000000000000)
  centralHi := (159173766309503004263/50000000000000000000)
  directionLo := (80551607870600552713/25000000000000000000)
  directionHi := (322206431482402210853/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree043.table
  base := (-2521129430072167255372443135958207438043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-541655606064583228072550899133500000000000000)
      constant := (6835598624319986050433935902350375038883261397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree043.table
  base := (-2521828611401030463447052763613544146839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2200335186136967538246822493985500000000000000)
      constant := (27887511437756905123683390316287358431991131601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80551607870600552713/25000000000000000000)
  centralHi := (322206431482402210853/100000000000000000000)
  directionLo := (163009829038496024159/50000000000000000000)
  directionHi := (326019658076992048319/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree044.table
  base := (-1506345262388823155970198019747362957093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-553380041033742719852606125749100000000000000)
      constant := (7145079126947138242912338693889181138016866347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree044.table
  base := (-75347113348000006933603964884171174167/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2247977633302405592324868508857100000000000000)
      constant := (29150149436606564589522291300554525428170303060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163009829038496024159/50000000000000000000)
  centralHi := (326019658076992048319/100000000000000000000)
  directionLo := (329788796681533228967/100000000000000000000)
  directionHi := (41223599585191653621/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree045.table
  base := (-109573772059897596592644026514940102263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-565104476002902211632661352364700000000000000)
      constant := (7461436575605763088954371604840400637799899108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree045.table
  base := (-219402292410609647646127693726889826599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2295620080467843646402914523728700000000000000)
      constant := (30440843394915880178910640216747093446131882882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329788796681533228967/100000000000000000000)
  centralHi := (41223599585191653621/12500000000000000000)
  directionLo := (33351534204691171667/10000000000000000000)
  directionHi := (333515342046911716671/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree046.table
  base := (682938318457601147295059200984192500971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-576828910972061703412716578980300000000000000)
      constant := (7784670314643656665773568105679995788800191291) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree046.table
  base := (682503717679638265434280761328977637391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2343262527633281700480960538600300000000000000)
      constant := (31759590726420699567582325058614741772479645031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33351534204691171667/10000000000000000000)
  centralHi := (333515342046911716671/100000000000000000000)
  directionLo := (337200706322930727081/100000000000000000000)
  directionHi := (168600353161465363541/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree047.table
  base := (464321463166773154248108641370656241419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-588553345941221195192771805595900000000000000)
      constant := (8114779796679831519793068717314287872353119596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree047.table
  base := (74276612526044741609406383056284401391/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2390904974798719754559006553471900000000000000)
      constant := (33106389273884073177818495832692760212624225775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337200706322930727081/100000000000000000000)
  centralHi := (168600353161465363541/50000000000000000000)
  directionLo := (85211556327728455587/25000000000000000000)
  directionHi := (340846225310913822349/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree048.table
  base := (3084689820507308282786938797410429516663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-600277780910380686972827032211500000000000000)
      constant := (8451764564721051689576851384507088012201487623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree048.table
  base := (385546755302439588102509462346526633057/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2438547421964157808637052568343500000000000000)
      constant := (34481237237909916333344066864973160478798234696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85211556327728455587/25000000000000000000)
  centralHi := (340846225310913822349/100000000000000000000)
  directionLo := (344453164120629158081/100000000000000000000)
  directionHi := (172226582060314579041/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree049.table
  base := (4365102054486179241901115361507284248957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-612002215879540178752882258827100000000000000)
      constant := (8795624237232612497346015874042599198535988397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree049.table
  base := (4364833061487011548953868579608594011421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2486189869129595862715098583215100000000000000)
      constant := (35884133117569694844761893376311338960719940261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344453164120629158081/100000000000000000000)
  centralHi := (172226582060314579041/50000000000000000000)
  directionLo := (8700568057486531951/2500000000000000000)
  directionHi := (348022722299461278041/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree050.table
  base := (5698482340073913466661016462971203592249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-623726650848699670532937485442700000000000000)
      constant := (9146358495675223460449356845438194903654204329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree050.table
  base := (5698253295979640348301243750076956585697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2533832316295033916793144598086700000000000000)
      constant := (37315075660881392572421548196631215765962317577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8700568057486531951/2500000000000000000)
  centralHi := (348022722299461278041/100000000000000000000)
  directionLo := (351556038492788228041/100000000000000000000)
  directionHi := (175778019246394114021/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree051.table
  base := (1771199275543896136915688160176237051637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-635451085817859162312992712058300000000000000)
      constant := (9503967074100557666797986090272523894744066708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree051.table
  base := (3542301076026467598320003071181653672819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2581474763460471970871190612958300000000000000)
      constant := (38774063823505638920139765973764962730661587158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351556038492788228041/100000000000000000000)
  centralHi := (175778019246394114021/50000000000000000000)
  directionLo := (17752709734344617387/5000000000000000000)
  directionHi := (355054194686892347741/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree052.table
  base := (1065502288570969095530845801334948988273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-647175520787018654093047938673900000000000000)
      constant := (9868449750465373250364559253714593047488883464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree052.table
  base := (4261926220597841702190406383986145233719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2629117210625910024949236627829900000000000000)
      constant := (40261096734295346122129414569018200158867180958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17752709734344617387/5000000000000000000)
  centralHi := (355054194686892347741/100000000000000000000)
  directionLo := (358518220079220674217/100000000000000000000)
  directionHi := (179259110039610337109/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree053.table
  base := (1252015319307303817083721157546870833769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-658899955756178145873103165289500000000000000)
      constant := (10239806339380312877529929747456730110994273992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree053.table
  base := (5007990741718465923358846374734674974743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2676759657791348079027282642701500000000000000)
      constant := (41776173666561564869318585869507047441731480926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358518220079220674217/100000000000000000000)
  centralHi := (179259110039610337109/50000000000000000000)
  directionLo := (361949094615233657427/100000000000000000000)
  directionHi := (90487273653808414357/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree054.table
  base := (11561090298251496453078547486554959299951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-670624390725337637653158391905100000000000000)
      constant := (10618036686056393670590808265755601832614911871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree054.table
  base := (11560970359352553764691639639878690333961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2724402104956786133105328657573100000000000000)
      constant := (43319294014107026716223474349663953116990444401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361949094615233657427/100000000000000000000)
  centralHi := (90487273653808414357/25000000000000000000)
  directionLo := (11417117257071546783/3125000000000000000)
  directionHi := (365347752226289497057/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree055.table
  base := (13158905223539528270682036531250524576341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-682348825694497129433213618520700000000000000)
      constant := (11003140661251352437962046786247535405169197061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree055.table
  base := (1644850410772583725243587722415311100763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2772044552122224187183374672444700000000000000)
      constant := (44890457271236258286387143044354771863836378264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11417117257071546783/3125000000000000000)
  centralHi := (365347752226289497057/100000000000000000000)
  directionLo := (92178770949720670391/25000000000000000000)
  directionHi := (73743016759776536313/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree056.table
  base := (7404776853237498461770725739468659790471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-694073260663656621213268845136300000000000000)
      constant := (11395118157050692901912344193616662508400641582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree056.table
  base := (14809467097452581647552106711569591764589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2819686999287662241261420687316300000000000000)
      constant := (46489663016082436017228866827309401289729196149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92178770949720670391/25000000000000000000)
  centralHi := (73743016759776536313/20000000000000000000)
  directionLo := (372051939901987252203/100000000000000000000)
  directionHi := (93012984975496813051/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree057.table
  base := (16513024371113967076367004827408660745271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-705797695632816112993324071751900000000000000)
      constant := (11793969083345563150650870081058004001763291591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree057.table
  base := (4128237702240786060483616052362234753607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2867329446453100295339466702187900000000000000)
      constant := (48116910896700642855895046948259053454961287548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372051939901987252203/100000000000000000000)
  centralHi := (93012984975496813051/25000000000000000000)
  directionLo := (37535913329616316937/10000000000000000000)
  directionHi := (375359133296163169371/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree058.table
  base := (9134653859100804814338658479343934202399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-717522130601975604773379298367500000000000000)
      constant := (12199693364892365682872711440617566605634404958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree058.table
  base := (18269245256754619889062533324532796420489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2914971893618538349417512717059500000000000000)
      constant := (49772200619468508928867082333975155330108888049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37535913329616316937/10000000000000000000)
  centralHi := (375359133296163169371/100000000000000000000)
  directionLo := (94659360311349309667/25000000000000000000)
  directionHi := (378637441245397238669/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree059.table
  base := (5019598953817251247118803687648491102397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-729246565571135096553434524983100000000000000)
      constant := (12612290938858014186489658663994554792088346548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree059.table
  base := (2007834279516518907251676059232801799791/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-2962614340783976403495558731931100000000000000)
      constant := (51455531939411383877019374071901882024671034310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94659360311349309667/25000000000000000000)
  centralHi := (378637441245397238669/100000000000000000000)
  directionLo := (7637752153006184109/2000000000000000000)
  directionHi := (381887607650309205451/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree060.table
  base := (5485070509478599067793821274115451812829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-740971000540294588333489751598700000000000000)
      constant := (13031761752770622345218910693971073975237674036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree060.table
  base := (10970118522487976538162859676645517052931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3010256787949414457573604746802700000000000000)
      constant := (53166904652132714966593481680440798023785924342) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7637752153006184109/2000000000000000000)
  centralHi := (381887607650309205451/100000000000000000000)
  directionLo := (3851103450193091839/1000000000000000000)
  directionHi := (385110345019309183901/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree061.table
  base := (23854960853814750873572300908565826747137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-752695435509454080113544978214300000000000000)
      constant := (13458105762808659417810478926785249913664072177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree061.table
  base := (23854922683343925202397894959070720716517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3057899235114852511651650761674300000000000000)
      constant := (54906318587083290060795854938744084962477921197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3851103450193091839/1000000000000000000)
  centralHi := (385110345019309183901/100000000000000000000)
  directionLo := (388306336292502718559/100000000000000000000)
  directionHi := (2426914601828141991/625000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree062.table
  base := (6455606910602472213177584839889450915793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-764419870478613571893600204829900000000000000)
      constant := (13891322932372668218936209497721657362815985412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree062.table
  base := (5164479053717554192074326105964204847979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3105541682280290565729696776545900000000000000)
      constant := (56673773601947197521220815998724595437670475695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (388306336292502718559/100000000000000000000)
  centralHi := (2426914601828141991/625000000000000000)
  directionLo := (391476236531569141781/100000000000000000000)
  directionHi := (195738118265784570891/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree063.table
  base := (3480334818045897687732270461994038943111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-776144305447773063673655431445500000000000000)
      constant := (14331413230892874996610084280455938259747057848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree063.table
  base := (2784265109404345908447396995298462682231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3153184129445728619807742791417500000000000000)
      constant := (58469269577959215122081733573579880428013634710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391476236531569141781/100000000000000000000)
  centralHi := (195738118265784570891/50000000000000000000)
  directionLo := (197310337243728772309/50000000000000000000)
  directionHi := (394620674487457544619/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree064.table
  base := (299157103359080153927155471831614082061/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-787868740416932555453710658061100000000000000)
      constant := (14778376632833729353866537179023421514400518100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree064.table
  base := (29915687066166502215639019567332317277557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3200826576611166673885788806289100000000000000)
      constant := (60292806415999083943906777364510494777890203837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197310337243728772309/50000000000000000000)
  centralHi := (394620674487457544619/100000000000000000000)
  directionLo := (198870127028263587451/50000000000000000000)
  directionHi := (397740254056527174903/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree065.table
  base := (4005190040486207832512385288793882485867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-799593175386092047233765884676700000000000000)
      constant := (15232213116862847743285450422530790745364420056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree065.table
  base := (32041500602857773128148770896345770686087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3248469023776604727963834821160700000000000000)
      constant := (62144384033333765851256716661920314838552913567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198870127028263587451/50000000000000000000)
  centralHi := (397740254056527174903/100000000000000000000)
  directionLo := (400835555634683732551/100000000000000000000)
  directionHi := (50104444454335466569/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree066.table
  base := (1368804250328577980984888285886338982781/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-811317610355251539013821111292300000000000000)
      constant := (15692922665157206490860303053927642277065207525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree066.table
  base := (34220089548657397506618338157478075884181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3296111470942042782041880836032300000000000000)
      constant := (64024002360900171011192304340450755029405043421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (400835555634683732551/100000000000000000000)
  centralHi := (50104444454335466569/12500000000000000000)
  directionLo := (40390713737811132389/10000000000000000000)
  directionHi := (403907137378111323891/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree067.table
  base := (9112866564676084450925745797470324204441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-823042045324411030793876337907900000000000000)
      constant := (16160505262823915356146863538326149752093508644) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree067.table
  base := (7290290420801596317307570722039069464007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3343753918107480836119926850903900000000000000)
      constant := (65931661341038680970104879727827369123481241435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40390713737811132389/10000000000000000000)
  centralHi := (403907137378111323891/100000000000000000000)
  directionLo := (406955536378355896803/100000000000000000000)
  directionHi := (101738884094588974201/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree068.table
  base := (1936779937702586638338928176754612059001/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-834766480293570522573931564523500000000000000)
      constant := (16634960897416646881284343565404265642386938420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree068.table
  base := (9683896691563202564297321160006973437917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3391396365272918890197972865775500000000000000)
      constant := (67867360925602671919131926341049933743697194388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406955536378355896803/100000000000000000000)
  centralHi := (101738884094588974201/25000000000000000000)
  directionLo := (409981269758766181703/100000000000000000000)
  directionHi := (51247658719845772713/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree069.table
  base := (8214500486170390576633833060572855275681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-846490915262730014353986791139100000000000000)
      constant := (17116289558531922583868228574970087933193346005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree069.table
  base := (41072492280421976791908817330182167714213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3439038812438356944276018880647100000000000000)
      constant := (69831101074381653076844408918410466835731098733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409981269758766181703/100000000000000000000)
  centralHi := (51247658719845772713/12500000000000000000)
  directionLo := (206492417849315390813/50000000000000000000)
  directionHi := (412984835698630781627/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree070.table
  base := (43462176191052238894848957791798447139507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-858215350231889506134042017754700000000000000)
      constant := (17604491237472066557815695962037835499792034947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree070.table
  base := (5432770949772808010805447318260356230029/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3486681259603794998354064895518700000000000000)
      constant := (71822881753785986242204961151804040591730873512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206492417849315390813/50000000000000000000)
  centralHi := (412984835698630781627/100000000000000000000)
  directionLo := (207983357195377484851/50000000000000000000)
  directionHi := (415966714390754969703/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree071.table
  base := (45904619116427207199790943652893843504977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-869939785201048997914097244370300000000000000)
      constant := (18099565926963815539615089880606072134402922817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree071.table
  base := (22952305921798826323994724159996956952721/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3534323706769233052432110910390300000000000000)
      constant := (73842702935749786190044646233344424995444267122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207983357195377484851/50000000000000000000)
  centralHi := (415966714390754969703/100000000000000000000)
  directionLo := (52365921117211151727/12500000000000000000)
  directionHi := (418927368937689213817/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree072.table
  base := (12099957609730063367651241398992956645533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-881664220170208489694152470985900000000000000)
      constant := (18601513620923393166389152894779292838357067572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree072.table
  base := (24199912142283238360299993184805877130549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3581966153934671106510156925261900000000000000)
      constant := (75890564596815802672477184269946330218279841018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52365921117211151727/12500000000000000000)
  centralHi := (418927368937689213817/100000000000000000000)
  directionLo := (8437344923826917473/2000000000000000000)
  directionHi := (421867246191345873651/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree073.table
  base := (25473904757941044972488645294022013891487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-893388655139367981474207697601500000000000000)
      constant := (19110334314260374429772597925203196744068937054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree073.table
  base := (10189560861799981044866797195225837945019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3629608601100109160588202940133500000000000000)
      constant := (77966466717372091044670179057132455367981768895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8437344923826917473/2000000000000000000)
  centralHi := (421867246191345873651/100000000000000000000)
  directionLo := (42478677754031431893/10000000000000000000)
  directionHi := (424786777540314318931/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree074.table
  base := (53548555809397617776994123343592193371277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-905113090108527473254262924217100000000000000)
      constant := (19626028002713933831806941799421193763693885117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree074.table
  base := (26774275702474388049040469561797317872777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3677251048265547214666248955005100000000000000)
      constant := (80070409281015288205023588807563695723923295714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42478677754031431893/10000000000000000000)
  centralHi := (424786777540314318931/100000000000000000000)
  directionLo := (106921594912200542061/25000000000000000000)
  directionHi := (85537275929760433649/20000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree075.table
  base := (28101034434512961742541833319383352372023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-916837525077686965034318150832700000000000000)
      constant := (20148594682716128896804654311623171068277588366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree075.table
  base := (1124041302880548439718644228920354182773/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3724893495430985268744294969876700000000000000)
      constant := (82202392274019488985786744967519353418511484650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106921594912200542061/25000000000000000000)
  centralHi := (85537275929760433649/20000000000000000000)
  directionLo := (430566455150786447601/100000000000000000000)
  directionHi := (215283227575393223801/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree076.table
  base := (58908348317389711402417516300791266007827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-928561960046846456814373377448300000000000000)
      constant := (20678034351277754065788787672356567618047997667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree076.table
  base := (58908345167586296503890179134461193313679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3772535942596423322822340984748300000000000000)
      constant := (84362415684893203271269979672537271094963588839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430566455150786447601/100000000000000000000)
  centralHi := (215283227575393223801/50000000000000000000)
  directionLo := (1354460604070777657/312500000000000000)
  directionHi := (433427393302648850241/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree077.table
  base := (61667393838143586598001280557110102403507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-940286395016005948594428604063900000000000000)
      constant := (21214347005893037465510935304390969121138178947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree077.table
  base := (61667391175177533853413098445147881537983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3820178389761861376900386999619900000000000000)
      constant := (86550479504009780993422216911323083272358513303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1354460604070777657/312500000000000000)
  centralHi := (433427393302648850241/100000000000000000000)
  directionLo := (218134785298645060787/50000000000000000000)
  directionHi := (17450782823891604863/4000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree078.table
  base := (64479205165928327498523486864407205294477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-952010829985165440374483830679500000000000000)
      constant := (21757532644460068701888897033710769473137552317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree078.table
  base := (64479202914933044880169171594678000740829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3867820836927299430978433014491500000000000000)
      constant := (88766583723299116707649511551098877821736901989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218134785298645060787/50000000000000000000)
  centralHi := (17450782823891604863/4000000000000000000)
  directionLo := (439093351342466543309/100000000000000000000)
  directionHi := (43909335134246654331/10000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree079.table
  base := (67343782077983174374690380005205324168849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-963735264954324932154539057295100000000000000)
      constant := (22307591265214359797106937025238331372741452929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree079.table
  base := (67343780175537867507350958394516405230537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3915463284092737485056479029363100000000000000)
      constant := (91010728335990467714048876400783800139991636017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439093351342466543309/100000000000000000000)
  centralHi := (43909335134246654331/10000000000000000000)
  directionLo := (220949544102931801737/50000000000000000000)
  directionHi := (17675963528234544139/4000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree080.table
  base := (878264054839279117538654423212732901193/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-975459699923484423934594283910700000000000000)
      constant := (22864522866673370466605827788877444584827980240) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree080.table
  base := (7026112277953413207067526682603945894171/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-3963105731258175539134525044234700000000000000)
      constant := (93282913336397906410707013704909130303951330110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220949544102931801737/50000000000000000000)
  centralHi := (17675963528234544139/4000000000000000000)
  directionLo := (444687122729215622227/100000000000000000000)
  directionHi := (111171780682303905557/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree081.table
  base := (36615615967993543190623538420480369556719/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-987184134892643915714649510526300000000000000)
      constant := (23428327447590187138555706776191750014517542398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree081.table
  base := (18307807644433727512269890904557904554153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4010748178423613593212571059106300000000000000)
      constant := (95583138719741334420880558834938259279278465092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444687122729215622227/100000000000000000000)
  centralHi := (111171780682303905557/25000000000000000000)
  directionLo := (89491557162718614353/20000000000000000000)
  directionHi := (223728892906796535883/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree082.table
  base := (76254104591962761177630160554947377210311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-998908569861803407494704737141900000000000000)
      constant := (23999005006914844159950769306648338174882873431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree082.table
  base := (38127051722281918656163715235729456374021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4058390625589051647290617073977900000000000000)
      constant := (97911404481997159461472606712132615023360013722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89491557162718614353/20000000000000000000)
  centralHi := (223728892906796535883/50000000000000000000)
  directionLo := (225105699088904782217/50000000000000000000)
  directionHi := (90042279635561912887/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree083.table
  base := (39664871121650555682550653663105312284101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1010633004830962899274759963757500000000000000)
      constant := (24576555543762025282525637082381214357204728042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree083.table
  base := (1983243531854173727803715832685768653829/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4106033072754489701368663088849500000000000000)
      constant := (100267710619773714647983830766389688537493399560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225105699088904782217/50000000000000000000)
  centralHi := (90042279635561912887/20000000000000000000)
  directionLo := (22647413539587310077/5000000000000000000)
  directionHi := (452948270791746201541/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree084.table
  base := (16491628959123049032759638826944129935799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1022357439800122391054815190373100000000000000)
      constant := (25160979057384091936492020642748722266107319395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree084.table
  base := (41229071988584320936070378968026440246731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4153675519919927755446709103721100000000000000)
      constant := (102652057130207316266222721244644670343891015942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22647413539587310077/5000000000000000000)
  centralHi := (452948270791746201541/100000000000000000000)
  directionLo := (113917176321562648801/25000000000000000000)
  directionHi := (91133741057250119041/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree085.table
  base := (42819656084527992819327327037920109416581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1034081874769281882834870416988700000000000000)
      constant := (25752275547148558791347260879699230373377476202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree085.table
  base := (21409827869491231833860355874505589103873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4201317967085365809524755118592700000000000000)
      constant := (105064444010875536928451150601784634321908779172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113917176321562648801/25000000000000000000)
  centralHi := (91133741057250119041/20000000000000000000)
  directionLo := (229186497170569997071/50000000000000000000)
  directionHi := (458372994341139994143/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree086.table
  base := (88873244295936993867937144449115139891573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1045806309738441374614925643604300000000000000)
      constant := (26350445012519282356492306401502441023081149733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree086.table
  base := (88873243712464869225173428616187620545043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4248960414250803863602801133464300000000000000)
      constant := (107504871259724838945421696428484267549883722763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229186497170569997071/50000000000000000000)
  centralHi := (458372994341139994143/100000000000000000000)
  directionLo := (461061422052721315139/100000000000000000000)
  directionHi := (23053071102636065757/5000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree087.table
  base := (92159941118751263771270297515135139880569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1057530744707600866394980870219900000000000000)
      constant := (26955487453040749636764503920294485442993987049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree087.table
  base := (92159940626205876295226735051995300421741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4296602861416241917680847148335900000000000000)
      constant := (109973338875010186431017746989542081420813003381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461061422052721315139/100000000000000000000)
  centralHi := (23053071102636065757/5000000000000000000)
  directionLo := (463734264282134395987/100000000000000000000)
  directionHi := (115933566070533598997/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree088.table
  base := (47749701294257190864119228187540408640887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1069255179676760358175036096835500000000000000)
      constant := (27567402868324955091876541017779815153688931854) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree088.table
  base := (95499402172780856460515087714550834839371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4344245308581679971758893163207500000000000000)
      constant := (112469846855244649747741053585590723299088286211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463734264282134395987/100000000000000000000)
  centralHi := (115933566070533598997/25000000000000000000)
  directionLo := (466391788985727454551/100000000000000000000)
  directionHi := (58298973623215931819/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree089.table
  base := (98891628663380613671047544522603573401439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 890000000000000000000000000000000000000000
      center := (2891)
      previous := (0)
      next := (2360)
      square := (119637091522035630408726802200000000000000)
      linear := (-12145838366808088201742599139900000000000000)
      constant := (316698778180229647890757537235411718032728071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree089.table
  base := (49445814156262760796810831607726081515757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4391887755747118025836939178079100000000000000)
      constant := (114994395199157345439701053778442402755692740074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466391788985727454551/100000000000000000000)
  centralHi := (58298973623215931819/12500000000000000000)
  directionLo := (469034256528584680471/100000000000000000000)
  directionHi := (58629282066073085059/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree090.table
  base := (102336619307486789653896447365606899484349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1092704049615079341735146550066700000000000000)
      constant := (28811852621903128178826452680125972250815528429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree090.table
  base := (102336619011422711024813763156567058205711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4439530202912556079914985192950700000000000000)
      constant := (117546983905658329661878842178722565111969186151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469034256528584680471/100000000000000000000)
  centralHi := (58629282066073085059/12500000000000000000)
  directionLo := (471661919982244312749/100000000000000000000)
  directionHi := (1886647679928977251/400000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree091.table
  base := (26458593622496598014073929841684035086527/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1104428484584238833515201776682300000000000000)
      constant := (29444386959668688375451739718201416967681521468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree091.table
  base := (21166874848037551384970688820086005090587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4487172650077994133993031207822300000000000000)
      constant := (120127612973809292372357805840751378445537490335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471661919982244312749/100000000000000000000)
  centralHi := (1886647679928977251/400000000000000000)
  directionLo := (14821094543986586347/3125000000000000000)
  directionHi := (94855005081514152621/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree092.table
  base := (54692447092121230779943314079952700099299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1116152919553398325295257003297900000000000000)
      constant := (30083794271126127897392562409106210674973094758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree092.table
  base := (27346223493376220686215791018651987448161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4534815097243432188071077222693900000000000000)
      constant := (122736282402799090774735359442190113319306106404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14821094543986586347/3125000000000000000)
  centralHi := (94855005081514152621/20000000000000000000)
  directionLo := (476873812123675699807/100000000000000000000)
  directionHi := (14902306628864865619/3125000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree093.table
  base := (7061761147947069856572839671205537154113/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1127877354522557817075312229913500000000000000)
      constant := (30730074556092456749529191636175204956763665168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree093.table
  base := (14123522273673700463727472554673018445909/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4582457544408870242149123237565500000000000000)
      constant := (125372992191923319992334986469655525472202962152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476873812123675699807/100000000000000000000)
  centralHi := (14902306628864865619/3125000000000000000)
  directionLo := (239729256481859971593/50000000000000000000)
  directionHi := (479458512963719943187/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree094.table
  base := (116644227018587817536492146628194530180733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1139601789491717308855367456529100000000000000)
      constant := (31383227814408220901110003019000528873561586093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree094.table
  base := (4665769074746250012160567334053140408977/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4630099991574308296227169252437100000000000000)
      constant := (128037742340567251988203851334846516796100801425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239729256481859971593/50000000000000000000)
  centralHi := (479458512963719943187/100000000000000000000)
  directionLo := (120507338629592508311/25000000000000000000)
  directionHi := (96405870903674006649/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree095.table
  base := (60176520060458043979755943585662357472997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1151326224460876800635422683144700000000000000)
      constant := (32043254045933769374754611579595563067087218474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree095.table
  base := (120353039994473198779826533150970516485757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4677742438739746350305215267308700000000000000)
      constant := (130730532848191584705844466755041746318720140037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120507338629592508311/25000000000000000000)
  centralHi := (96405870903674006649/20000000000000000000)
  directionLo := (242293278683814977153/50000000000000000000)
  directionHi := (484586557367629954307/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree096.table
  base := (124114617658613482991547465697213589548029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1163050659430036292415477909760300000000000000)
      constant := (32710153250546133033834231290651628842809937709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree096.table
  base := (62057308775995640630110313446879340611819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4725384885905184404383261282180300000000000000)
      constant := (133451363714320535957308715751758921905086585158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242293278683814977153/50000000000000000000)
  centralHi := (484586557367629954307/100000000000000000000)
  directionLo := (3805705752357182261/781250000000000000)
  directionHi := (487130336301719329409/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree097.table
  base := (127928959617932034614856361620331012185523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1174775094399195784195533136375900000000000000)
      constant := (33383925428136414223680323646610741947521527683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree097.table
  base := (31982239882008314330223323486410475467181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4773027333070622458461307297051900000000000000)
      constant := (136200234938531893782161500434712412177775785684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell198.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3805705752357182261/781250000000000000)
  centralHi := (487130336301719329409/100000000000000000000)
  directionLo := (244830450265812028487/50000000000000000000)
  directionHi := (19586436021264962279/4000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 49
  qDenominator := 89
  table := BinomialMassData.Q49_89.Degree098.table
  base := (26359213197324913540480516257971666774793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 79210000000000000000000000000000000000000000
      center := (257299)
      previous := (0)
      next := (210040)
      square := (10647701145461171106376685395800000000000000)
      linear := (-1186499529368355275975588362991500000000000000)
      constant := (34064570578607603070111636541764767862615676765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q49_89.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 99
  qDenominator := 179
  table := BinomialMassData.Q99_179.Degree098.table
  base := (131796065910834238542781409514090942593403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320410000000000000000000000000000000000000000
      center := (1045539)
      previous := (0)
      next := (844880)
      square := (43070697184916220605910286171800000000000000)
      linear := (-4820669780236060512539353311923500000000000000)
      constant := (138977146520448699390567619222424787891635225523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q99_179.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell198.Kernel098
