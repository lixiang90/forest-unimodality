import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell011.Parameters
import ForestUnimodality.BinomialMassData.Q1_3.Batch000_049
import ForestUnimodality.BinomialMassData.Q1_3.Batch050_099
import ForestUnimodality.BinomialMassData.Q1_3.Batch100_149
import ForestUnimodality.BinomialMassData.Q1_3.Batch150_199
import ForestUnimodality.BinomialMassData.Q29_85.Batch000_049
import ForestUnimodality.BinomialMassData.Q29_85.Batch050_099
import ForestUnimodality.BinomialMassData.Q29_85.Batch100_149
import ForestUnimodality.BinomialMassData.Q29_85.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree000.table
  base := (183105325452354839943325259/20000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (382393601364332536007850650000000000000)
      constant := (91552662726177419971662629500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree000.table
  base := (183105325452354839943325259/20000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (32503456115968265560667305250000000000000)
      constant := (7781976331725080697591323507500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree001.table
  base := (63165424145688408915330558839657823913879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (2345398024587075913593992010000000000000)
      constant := (567524327238384668781697588246920415224911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree001.table
  base := (6250156400281591597582048871157939254133/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (372425692927422168909679098210000000000000)
      constant := (90156968519598012715532431627430222222221850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (30010543871903535651/100000000000000000000)
  directionHi := (7502635967975883913/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree002.table
  base := (10916704980117657106683918019230252979623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (1249253636895159003117328170000000000000)
      constant := (391437780601177605231558387352289107266428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree002.table
  base := (42762650928096865300975081086194872741253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (192292631883383823288014007170000000000000)
      constant := (61537904824161258762300034667243591111110585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30010543871903535651/100000000000000000000)
  centralHi := (7502635967975883913/25000000000000000000)
  directionLo := (10610329539459689051/25000000000000000000)
  directionHi := (8488263631567751241/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree003.table
  base := (6042592368755051361458268262634571333077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (17012138800360232515629370000000000000)
      constant := (30013258973692910423029601303172856665385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree003.table
  base := (29286444419615201099990611356104654262749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (12159570839345477666348916130000000000000)
      constant := (42029909278940788405244084585053225409672305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10610329539459689051/25000000000000000000)
  centralHi := (8488263631567751241/20000000000000000000)
  directionLo := (25989893374455870263/50000000000000000000)
  directionHi := (51979786748911740527/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree004.table
  base := (10436741835518083450384825784377146847819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-943035138488674817835999510000000000000)
      constant := (186195681523465290102770426558788643260742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree004.table
  base := (20026122334091548749094636522059867939907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-167973490204692867955316174910000000000000)
      constant := (28675323886897905313013401246944509173165615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25989893374455870263/50000000000000000000)
  centralHi := (51979786748911740527/100000000000000000000)
  directionLo := (60021087743807071303/100000000000000000000)
  directionHi := (7502635967975883913/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree005.table
  base := (14346963668440453994346203093804985450039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-2039179526180591728312663350000000000000)
      constant := (127954037277548751702650834094244869050351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree005.table
  base := (106380048532912689296864872069348737573/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-348106551248731213576981265950000000000000)
      constant := (19501668074325203079181170126896742501502080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60021087743807071303/100000000000000000000)
  centralHi := (7502635967975883913/12500000000000000000)
  directionLo := (33552808069658023357/50000000000000000000)
  directionHi := (13421123227863209343/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree006.table
  base := (9773865059641437643952235476587543537499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-348369323763612070976591910000000000000)
      constant := (9739840782040717178920976736587543537499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree006.table
  base := (4582803484432256726153597855151452104723/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-528239612292769559198646356990000000000000)
      constant := (13219410713232208843125724726015696582649470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33552808069658023357/50000000000000000000)
  centralHi := (13421123227863209343/20000000000000000000)
  directionLo := (18377629847393068317/25000000000000000000)
  directionHi := (73510519389572273269/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree007.table
  base := (1628869174655673833593713144995255575399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-4231468301564425549265991030000000000000)
      constant := (59560870491770596188768230929829200714364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree007.table
  base := (3009433352285653636535394351060179326441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-708372673336807904820311448030000000000000)
      constant := (8883322538877100893285291754165918253414490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18377629847393068317/25000000000000000000)
  centralHi := (73510519389572273269/100000000000000000000)
  directionLo := (39700217897425097133/50000000000000000000)
  directionHi := (79400435794850194267/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree008.table
  base := (2080379387888939056210888152541998654867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-5327612689256342459742654870000000000000)
      constant := (39961589351304035859358652105755975787606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree008.table
  base := (3759512615667611868117552588953346736049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-888505734380846250441976539070000000000000)
      constant := (5890964549963096153731432344909586033590805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39700217897425097133/50000000000000000000)
  centralHi := (79400435794850194267/100000000000000000000)
  directionLo := (84882636315677512409/100000000000000000000)
  directionHi := (8488263631567751241/10000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree009.table
  base := (60741561621253137448475804920701219233/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-713750786327584374468813190000000000000)
      constant := (2926698242295003255630476006828048769320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree009.table
  base := (1053289319343240229070989402620949099707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-1068638795424884596063641630110000000000000)
      constant := (3836340784780456528367686621012542898153230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84882636315677512409/100000000000000000000)
  centralHi := (8488263631567751241/10000000000000000000)
  directionLo := (18006326323142121391/20000000000000000000)
  directionHi := (22507907903927651739/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree010.table
  base := (226237751613593442740761483473977321229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-7519901464640176280695982550000000000000)
      constant := (16977963909880344017709811256328979455305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree010.table
  base := (435245254361425268676088389801381120393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-1248771856468922941685306721150000000000000)
      constant := (2445516430541366696324772706825991437935770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18006326323142121391/20000000000000000000)
  centralHi := (22507907903927651739/25000000000000000000)
  directionLo := (23725418113905901949/25000000000000000000)
  directionHi := (94901672455623607797/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree011.table
  base := (1685875039653462017812707303072329733/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-8616045852332093191172646390000000000000)
      constant := (10700419668647843325845465248212077407760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree011.table
  base := (-76887747666576378655955256382713784929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-1428904917512961287306971812190000000000000)
      constant := (1533335005620260347638763546984978580777595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23725418113905901949/25000000000000000000)
  centralHi := (94901672455623607797/100000000000000000000)
  directionLo := (19906742755520718719/20000000000000000000)
  directionHi := (24883428444400898399/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree012.table
  base := (-648601599459739590947229600842486228391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-1079132248891556677961034470000000000000)
      constant := (744875695594708692959138039157513771609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree012.table
  base := (-411186324094530696820640089717785948761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-1609037978556999632928636903230000000000000)
      constant := (974346641930145187378102284627598608080710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19906742755520718719/20000000000000000000)
  centralHi := (24883428444400898399/25000000000000000000)
  directionLo := (103959573497823481053/100000000000000000000)
  directionHi := (51979786748911740527/50000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree013.table
  base := (-1280528735469369696706982388736471903731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-10808334627715927012125974070000000000000)
      constant := (4436624514222363470423681311371752866421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree013.table
  base := (-284994333397734476048220931304886623193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-1789171039601037978550301994270000000000000)
      constant := (683285539332843139581880785984194147430575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103959573497823481053/100000000000000000000)
  centralHi := (51979786748911740527/50000000000000000000)
  directionLo := (108204554734709800683/100000000000000000000)
  directionHi := (27051138683677450171/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree014.table
  base := (-1803142430126070051131777382139754235419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-11904479015407843922602637910000000000000)
      constant := (3518570202832688769721961700742211881229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree014.table
  base := (-120309797645763915127268524786738546013/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-1969304100645076324171967085310000000000000)
      constant := (601958718132808980575745211638604816179440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108204554734709800683/100000000000000000000)
  centralHi := (27051138683677450171/25000000000000000000)
  directionLo := (112289173159411303957/100000000000000000000)
  directionHi := (56144586579705651979/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree015.table
  base := (-8772149031115158938109198191712531423/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-1444513711455528981453255750000000000000)
      constant := (409630123262510425457558012921591955712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree015.table
  base := (-2349959817494693439531732084183671744837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-2149437161689114669793632176350000000000000)
      constant := (690438106997694788930148752404594328710535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112289173159411303957/100000000000000000000)
  centralHi := (56144586579705651979/50000000000000000000)
  directionLo := (11623033662650944443/10000000000000000000)
  directionHi := (116230336626509444431/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree016.table
  base := (-525691823691924936785582016852781007249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-14096767790791677743555965590000000000000)
      constant := (4757802276563870963276301881624854673795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree016.table
  base := (-2719069238603608753510361277449522594487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-2329570222733153015415297267390000000000000)
      constant := (921140959073228412413729296773439850966285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11623033662650944443/10000000000000000000)
  centralHi := (116230336626509444431/100000000000000000000)
  directionLo := (120042175487614142607/100000000000000000000)
  directionHi := (7502635967975883913/6250000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree017.table
  base := (-1482889770961138301080187303249414549023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-15192912178483594654032629430000000000000)
      constant := (6603531793612549098782220351510538117586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree017.table
  base := (-761396210723481681005717972548246974417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (-147629604928070080060997785790000000000000)
      constant := (74991119909111490509014282899596028698220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120042175487614142607/100000000000000000000)
  centralHi := (7502635967975883913/6250000000000000000)
  directionLo := (123736642266091076331/100000000000000000000)
  directionHi := (30934160566522769083/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree018.table
  base := (-3267731738672323149306319195795482841231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-1809895174019501284945477030000000000000)
      constant := (1014772979293183097506559944204517158769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree018.table
  base := (-3338871970405070540607901992294422366287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-2689836344821229706658627449470000000000000)
      constant := (1738029428785729058765357278986559680715285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123736642266091076331/100000000000000000000)
  centralHi := (30934160566522769083/25000000000000000000)
  directionLo := (63661977236758134307/50000000000000000000)
  directionHi := (25464790894703253723/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree019.table
  base := (-3541544752219788581093937513956859054933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-17385200953867428474985957110000000000000)
      constant := (12281015945051948998053016364388268505603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree019.table
  base := (-3605610684692218699817873882821542891469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-2869969405865268052280292540510000000000000)
      constant := (2301029438228496645231822483700870521827295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63661977236758134307/50000000000000000000)
  centralHi := (25464790894703253723/20000000000000000000)
  directionLo := (13081292797832135631/10000000000000000000)
  directionHi := (130812927978321356311/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree020.table
  base := (-1896230841623150196579399951105594943523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-18481345341559345385462620950000000000000)
      constant := (16000521281717804999544017880099291016586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree020.table
  base := (-770127720489572417638125538830945824769/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-3050102466909306397901957631550000000000000)
      constant := (2956858710662548767005459432146416416043975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13081292797832135631/10000000000000000000)
  centralHi := (130812927978321356311/100000000000000000000)
  directionLo := (134211232278632093429/100000000000000000000)
  directionHi := (13421123227863209343/10000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree021.table
  base := (-2012172096028957293745305619164816434157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-2175276636583473588437698310000000000000)
      constant := (2250746431209079096013855571670367131686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree021.table
  base := (-2038760299115474284554702693853771747191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-3230235527953344743523622722590000000000000)
      constant := (3700366002350205761497483490080599650618010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134211232278632093429/100000000000000000000)
  centralHi := (13421123227863209343/10000000000000000000)
  directionLo := (68762794469895535221/50000000000000000000)
  directionHi := (137525588939791070443/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree022.table
  base := (-4240086082631825237094867524022390619693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-20673634116943179206415948630000000000000)
      constant := (25023561506748922934745599143798484422763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree022.table
  base := (-1072233706317133352413237112780748237287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-3410368588997383089145287813630000000000000)
      constant := (4527681381878372767779113207859275188481140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68762794469895535221/50000000000000000000)
  centralHi := (137525588939791070443/100000000000000000000)
  directionLo := (140761927937648789721/100000000000000000000)
  directionHi := (70380963968824394861/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree023.table
  base := (-27761856275830669084754733904899457847/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-21769778504635096116892612470000000000000)
      constant := (30281165316835565807104016886944780700320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree023.table
  base := (-2243467551370047847100857733766662266197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-3590501650041421434766952904670000000000000)
      constant := (5435837080532702508920585932856346050690670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140761927937648789721/100000000000000000000)
  centralHi := (70380963968824394861/50000000000000000000)
  directionLo := (17990689041579291727/12500000000000000000)
  directionHi := (143925512332634333817/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree024.table
  base := (-926299542966244355797884817163882468843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-2540658099147445891929919590000000000000)
      constant := (4001560276301231644698851674180587655785) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree024.table
  base := (-4673129998932660363996978006557551375831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-3770634711085459780388617995710000000000000)
      constant := (6422508717138443944828264246972338261924205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17990689041579291727/12500000000000000000)
  centralHi := (143925512332634333817/100000000000000000000)
  directionLo := (18377629847393068317/12500000000000000000)
  directionHi := (147021038779144546537/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree025.table
  base := (-4810255059306166989763628902775928438587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-23962067280018929937845940150000000000000)
      constant := (42209891415160901732857691125016644052717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree025.table
  base := (-4848805705294780069804780267220821902911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-3950767772129498126010283086750000000000000)
      constant := (7485837745052438495145214282615912350293605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18377629847393068317/12500000000000000000)
  centralHi := (147021038779144546537/100000000000000000000)
  directionLo := (75026359679758839129/50000000000000000000)
  directionHi := (150052719359517678259/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree026.table
  base := (-2489637893809547092276121642279890330309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-25058211667710846848322603990000000000000)
      constant := (48858751351632853110788252378961974054438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree026.table
  base := (-1003002182757481466589145096782570833221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-4130900833173536471631948177790000000000000)
      constant := (8624308804391109766563164366093925729978275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75026359679758839129/50000000000000000000)
  centralHi := (150052719359517678259/100000000000000000000)
  directionLo := (15302434881636849589/10000000000000000000)
  directionHi := (153024348816368495891/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree027.table
  base := (-321217013820943342357090525971162481609/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-2906039561711418195422140870000000000000)
      constant := (6216934600426791989650857574461400294256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree027.table
  base := (-5172615946979056523843127662961221182643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-4311033894217574817253613268830000000000000)
      constant := (9836664279042954493820425758263035391080865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15302434881636849589/10000000000000000000)
  centralHi := (153024348816368495891/100000000000000000000)
  directionLo := (7796968012336761079/5000000000000000000)
  directionHi := (155939360246735221581/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree028.table
  base := (-5291608612085493189520971171985580611847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-27250500443094680669275931670000000000000)
      constant := (63483993301703771238602546612129774493377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree028.table
  base := (-1330588596610761151900285785498987040989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-4491166955261613162875278359870000000000000)
      constant := (11121844143634529662341492551247854903083580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7796968012336761079/5000000000000000000)
  centralHi := (155939360246735221581/100000000000000000000)
  directionLo := (39700217897425097133/25000000000000000000)
  directionHi := (158800871589700388533/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree029.table
  base := (-5436334220691289804378378223887386975627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-28346644830786597579752595510000000000000)
      constant := (71447653703231814746390637675013517219357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree029.table
  base := (-1092970551153623744473288412762627256981/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-4671300016305651508496943450910000000000000)
      constant := (12478943071580095657504426388708018068312275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39700217897425097133/25000000000000000000)
  centralHi := (158800871589700388533/100000000000000000000)
  directionLo := (161611724701940975421/100000000000000000000)
  directionHi := (80805862350970487711/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree030.table
  base := (-2787103607950619183430984832915065335321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-3271421024275390498914362150000000000000)
      constant := (8870929898654051447670587834169869329358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree030.table
  base := (-112013040151252415215848427046019840713/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-4851433077349689854118608541950000000000000)
      constant := (13907179386360598444425068715625066508485750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161611724701940975421/100000000000000000000)
  centralHi := (80805862350970487711/50000000000000000000)
  directionLo := (3287490368327998963/2000000000000000000)
  directionHi := (164374518416399948151/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree031.table
  base := (-5705712202611634653341452578966147488401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-30538933606170431400705923190000000000000)
      constant := (88651778011601054099209141379304672604391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree031.table
  base := (-1432555837288464401098693045287136818863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-5031566138393728199740273632990000000000000)
      constant := (15405872193388079579313245786018349186971860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3287490368327998963/2000000000000000000)
  centralHi := (164374518416399948151/100000000000000000000)
  directionLo := (41772909169782852053/25000000000000000000)
  directionHi := (167091636679131408213/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree032.table
  base := (-5831273292237696072910738124724233770499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-31635077993862348311182587030000000000000)
      constant := (97884063471638631275066989837481896065509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree032.table
  base := (-5853980124629432150089278230082837639257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-5211699199437766545361938724030000000000000)
      constant := (16974424210455952876125650182682299611273635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41772909169782852053/25000000000000000000)
  centralHi := (167091636679131408213/100000000000000000000)
  directionLo := (169765272631355024819/100000000000000000000)
  directionHi := (8488263631567751241/5000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree033.table
  base := (-2975632015380137314637541755100783093499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-3636802486839362802406583430000000000000)
      constant := (11947984839352391835917946779798433813002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree033.table
  base := (-5972286920829053714126744320022702433219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-5391832260481804890983603815070000000000000)
      constant := (18612308609580838372879868939389194983998545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169765272631355024819/100000000000000000000)
  centralHi := (8488263631567751241/5000000000000000000)
  directionLo := (172397449328827792521/100000000000000000000)
  directionHi := (86198724664413896261/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree034.table
  base := (-3033007543992062640243925087326250462029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-33827366769246182132135914710000000000000)
      constant := (117592202230956945221312481968127491683478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree034.table
  base := (-3042733347109779863831512352533584169911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (-327762665972108425682662876830000000000000)
      constant := (1195238748156950351856217215233290691115130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172397449328827792521/100000000000000000000)
  centralHi := (86198724664413896261/50000000000000000000)
  directionLo := (8749501882760697073/5000000000000000000)
  directionHi := (174990037655213941461/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree035.table
  base := (-1543955083006953581149239476304874628577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-34923511156938099042612578550000000000000)
      constant := (128062434688927790686788594603024513371228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree035.table
  base := (-1238761293087499620693102390915517622589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-5752098382569881582226933997150000000000000)
      constant := (22094259792898093968204239078685385176794475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8749501882760697073/5000000000000000000)
  centralHi := (174990037655213941461/100000000000000000000)
  directionLo := (177544771880392580611/100000000000000000000)
  directionHi := (44386192970098145153/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree036.table
  base := (-6280941722148926752578695453253395738677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-4002183949403335105898804710000000000000)
      constant := (15437800366085088666767028906746604261323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree036.table
  base := (-787195244895679775989430025556988444539/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-5932231443613919927848599088190000000000000)
      constant := (23937542310104339598404624872169213581129160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177544771880392580611/100000000000000000000)
  centralHi := (44386192970098145153/25000000000000000000)
  directionLo := (18006326323142121391/10000000000000000000)
  directionHi := (180063263231421213911/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree037.table
  base := (-3190806661232908769750372728178839952779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-37115799932321932863565906230000000000000)
      constant := (150223401471405772388047334902780880849978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree037.table
  base := (-6396961452399942839871903622897542757277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-6112364504657958273470264179230000000000000)
      constant := (25848576410026859627805458966375050715734735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18006326323142121391/10000000000000000000)
  centralHi := (180063263231421213911/100000000000000000000)
  directionLo := (182547011777885681497/100000000000000000000)
  directionHi := (91273505888942840749/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree038.table
  base := (-3239022324833804672590930198045506783501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-38211944320013849774042570070000000000000)
      constant := (161910143568645609909852046495180877896982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree038.table
  base := (-649220901625981384128235499798176327779/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-6292497565701996619091929270270000000000000)
      constant := (27827067209898985394792672082528352063593450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182547011777885681497/100000000000000000000)
  centralHi := (91273505888942840749/50000000000000000000)
  directionLo := (46249354220169239959/25000000000000000000)
  directionHi := (184997416880676959837/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree039.table
  base := (-1314084701259786428875126412084991284127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-4367565411967307409391025990000000000000)
      constant := (19333193262620404532615007649575043579365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree039.table
  base := (-6583487283307462937475493189606874376517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-6472630626746034964713594361310000000000000)
      constant := (29872750805668031956266294368076066525932935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46249354220169239959/25000000000000000000)
  centralHi := (184997416880676959837/100000000000000000000)
  directionLo := (187415786410884895429/100000000000000000000)
  directionHi := (18741578641088489543/10000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree040.table
  base := (-6658918408759708522238052231851627354287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-40404233095397683594995897750000000000000)
      constant := (186487672208620561772692475913335353811417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree040.table
  base := (-1667739958968211624647956800937042507871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-6652763687790073310335259452350000000000000)
      constant := (31985390820867212357373290309383894304505620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187415786410884895429/100000000000000000000)
  centralHi := (18741578641088489543/10000000000000000000)
  directionLo := (189803344911247215593/100000000000000000000)
  directionHi := (94901672455623607797/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree041.table
  base := (-842960086215134166467360327605738760701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-41500377483089600505472561590000000000000)
      constant := (199375580109716159170596412302386809229528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree041.table
  base := (-3377386642835885172689723080176580726549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-6832896748834111655956924543390000000000000)
      constant := (34164775401567187187132671128127681700273390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189803344911247215593/100000000000000000000)
  centralHi := (94901672455623607797/50000000000000000000)
  directionLo := (192161240844727376953/100000000000000000000)
  directionHi := (96080620422363688477/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree042.table
  base := (-6824846334111431391335765619457998992687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-4732946874531279712883247270000000000000)
      constant := (23629026578057198846792010720542001007313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree042.table
  base := (-6835059097461154995039795309987108984697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-7013029809878150001578589634430000000000000)
      constant := (36410714581194206298188348437240627517112835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192161240844727376953/100000000000000000000)
  centralHi := (96080620422363688477/50000000000000000000)
  directionLo := (194490553051999849583/100000000000000000000)
  directionHi := (12155659565749990599/6250000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree043.table
  base := (-6902537593372318832049574983523558278521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-43692666258473434326425889270000000000000)
      constant := (226343549224042627945099664658287975493311) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree043.table
  base := (-6911935197124006841673308700414808472481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-7193162870922188347200254725470000000000000)
      constant := (38723037956847325451065195037702601757264955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194490553051999849583/100000000000000000000)
  centralHi := (12155659565749990599/6250000000000000000)
  directionLo := (196792296520875569721/100000000000000000000)
  directionHi := (98396148260437784861/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree044.table
  base := (-6976864412416232208809370621899495154501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-44788810646165351236902553110000000000000)
      constant := (240421520670087205148149577642904543609491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree044.table
  base := (-3492753697887850904267508044831059787199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-7373295931966226692821919816510000000000000)
      constant := (41101592631464826436659692929166237214994890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196792296520875569721/100000000000000000000)
  centralHi := (98396148260437784861/50000000000000000000)
  directionLo := (19906742755520718719/10000000000000000000)
  directionHi := (199067427555207187191/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree045.table
  base := (-7047925696339034921974427272948206780671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-5098328337095252016375468550000000000000)
      constant := (28321584821642861180782706977051793219329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree045.table
  base := (-1763967663779170734253634577195418318617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-7553428993010265038443584907550000000000000)
      constant := (43546241385389569060163840010760482118393740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19906742755520718719/10000000000000000000)
  centralHi := (199067427555207187191/100000000000000000000)
  directionLo := (12582303026121758759/6250000000000000000)
  directionHi := (40263369683589628029/20000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree046.table
  base := (-1423162087712320682739607437622799411461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-46981099421549185057855880790000000000000)
      constant := (269760976457350376402404389846974026484255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree046.table
  base := (-7123110214571542297607058686103776057909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-7733562054054303384065249998590000000000000)
      constant := (46056861047653017779712096373048043596321495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12582303026121758759/6250000000000000000)
  centralHi := (40263369683589628029/20000000000000000000)
  directionLo := (203541411512307626117/100000000000000000000)
  directionHi := (101770705756153813059/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree047.table
  base := (-7180598728093202795888993924793670134843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-48077243809241101968332544630000000000000)
      constant := (285020939056697696467050516786856968786413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree047.table
  base := (-3593651298620100876602058684160546359989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-7913695115098341729686915089630000000000000)
      constant := (48633341042375785503426186504058021019631790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203541411512307626117/100000000000000000000)
  centralHi := (101770705756153813059/50000000000000000000)
  directionLo := (205741923155952837253/100000000000000000000)
  directionHi := (102870961577976418627/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree048.table
  base := (-3621181325303841770607019448325713188487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-5463709799659224319867689830000000000000)
      constant := (33408166935751450729664674543348573623026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree048.table
  base := (-1449703301799298071971338559800629170399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-8093828176142380075308580180670000000000000)
      constant := (51275582089570189245312446552832454243867225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205741923155952837253/100000000000000000000)
  centralHi := (102870961577976418627/50000000000000000000)
  directionLo := (207919146995646962107/100000000000000000000)
  directionHi := (51979786748911740527/25000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree049.table
  base := (-7301167095717891279976842781614818452081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-50269532584624935789285872310000000000000)
      constant := (316718082546030846029466016055466633931271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree049.table
  base := (-1826703410741495764573524564945447798041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-8273961237186418420930245271710000000000000)
      constant := (53983495042669773216017018827413311727323020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207919146995646962107/100000000000000000000)
  centralHi := (51979786748911740527/25000000000000000000)
  directionLo := (105036903551662374781/50000000000000000000)
  directionHi := (210073807103324749563/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree050.table
  base := (-367853524051357126122580315357462177313/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-51365676972316852699762536150000000000000)
      constant := (333154153671071216262034545735656808083660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree050.table
  base := (-58897995199488216503558189301324223421/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-8454094298230456766551910362750000000000000)
      constant := (56756999847536820690690807654948312144581875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105036903551662374781/50000000000000000000)
  centralHi := (210073807103324749563/100000000000000000000)
  directionLo := (6631455962162305657/3125000000000000000)
  directionHi := (8488263631567751241/4000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree051.table
  base := (-741012540209311266748246860298476268721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-5829091262223196623359911110000000000000)
      constant := (38886804715207232075010045307015237312790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree051.table
  base := (-7414873533884233515363685134393302890069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (-507895727016146771304327967870000000000000)
      constant := (3505648506451393151163934528370569254344135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6631455962162305657/3125000000000000000)
  centralHi := (8488263631567751241/4000000000000000000)
  directionLo := (107159075581422161829/50000000000000000000)
  directionHi := (214318151162844323659/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree052.table
  base := (-1492075843252833246450986343553398284549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-53557965747700686520715863830000000000000)
      constant := (367198922627277182613964083700097077195295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree052.table
  base := (-7464730730679225377244232506446234782587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-8814360420318533457795240544830000000000000)
      constant := (62500504758000201673658294052977190739161785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107159075581422161829/50000000000000000000)
  centralHi := (214318151162844323659/100000000000000000000)
  directionLo := (108204554734709800683/50000000000000000000)
  directionHi := (216409109469419601367/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree053.table
  base := (-7507874567374463354361900601957410501409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-54654110135392603431192527670000000000000)
      constant := (384806810447800056840319428992383305487319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree053.table
  base := (-1877965281763536793087284455446466372273/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-8994493481362571803416905635870000000000000)
      constant := (65470382294936981165467895514901424368262060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108204554734709800683/50000000000000000000)
  centralHi := (216409109469419601367/100000000000000000000)
  directionLo := (109240028612265892517/50000000000000000000)
  directionHi := (43696011444906357007/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree054.table
  base := (-94408123218311832984538947998937036737/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-6194472724787168926852132390000000000000)
      constant := (44756062253340580878835419820085037061040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree054.table
  base := (-472268798508762971767801960988950964433/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-9174626542406610149038570726910000000000000)
      constant := (68505605123709425549424399591203453702309040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109240028612265892517/50000000000000000000)
  centralHi := (43696011444906357007/20000000000000000000)
  directionLo := (55132889542179204951/25000000000000000000)
  directionHi := (44106311633743363961/20000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree055.table
  base := (-7594739670998772215477023435565589907941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-56846398910776437252145855350000000000000)
      constant := (421191860863904290651396117829909690828531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree055.table
  base := (-759808206514603688150260666002400365613/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-9354759603450648494660235817950000000000000)
      constant := (71606126444801063931555687186715314716892150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/25000000000000000000)
  centralHi := (44106311633743363961/20000000000000000000)
  directionLo := (222564150059729020029/100000000000000000000)
  directionHi := (22256415005972902003/10000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree056.table
  base := (-7634175156437382581748563655210763810957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-57942543298468354162622519190000000000000)
      constant := (439968431863164262590746984943103125701387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree056.table
  base := (-3818617045079041526217892099711660161091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-9534892664494686840281900908990000000000000)
      constant := (74771904214366979124635610142761302134447010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222564150059729020029/100000000000000000000)
  centralHi := (22256415005972902003/10000000000000000000)
  directionLo := (112289173159411303957/50000000000000000000)
  directionHi := (44915669263764521583/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree057.table
  base := (-3835492184759578447696640195461060517957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-6559854187351141230344353670000000000000)
      constant := (51014891197355525700803498299077878964086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree057.table
  base := (-7673782992502036258528284012209836404887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-9715025725538725185903566000030000000000000)
      constant := (78002900658191548793357704033058786394938285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112289173159411303957/50000000000000000000)
  centralHi := (44915669263764521583/20000000000000000000)
  directionLo := (226574637545300888129/100000000000000000000)
  directionHi := (22657463754530088813/10000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree058.table
  base := (-7705192582122867050131354479648716852833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-60134832073852187983575846870000000000000)
      constant := (478688400156101749757367989543161548324503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree058.table
  base := (-3853876130316716158599212914971926537971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-9895158786582763531525231091070000000000000)
      constant := (81299081835456523681552496845503132305263810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226574637545300888129/100000000000000000000)
  centralHi := (22657463754530088813/10000000000000000000)
  directionLo := (228553492911991869479/100000000000000000000)
  directionHi := (5713837322799796737/2500000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree059.table
  base := (-7736822560192662484855310288876140627977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-61230976461544104894052510710000000000000)
      constant := (498631365109372972991123780190114734348207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree059.table
  base := (-3869581500553904342883633279085566742999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-10075291847626801877146896182110000000000000)
      constant := (84660417247189152163391061351580712112732890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228553492911991869479/100000000000000000000)
  centralHi := (5713837322799796737/2500000000000000000)
  directionLo := (28814420181612019929/12500000000000000000)
  directionHi := (230515361452896159433/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree060.table
  base := (-7765894813841936948421071588030254964481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-6925235649915113533836574950000000000000)
      constant := (57662525671665873029866171411969745035519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree060.table
  base := (-7768034181809641104634781302409827936211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-10255424908670840222768561273150000000000000)
      constant := (88086879484796366793995433523817798632175105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28814420181612019929/12500000000000000000)
  centralHi := (230515361452896159433/100000000000000000000)
  directionLo := (11623033662650944443/5000000000000000000)
  directionHi := (232460673253018888861/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree061.table
  base := (-3896213911216893129644097842290803984789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-63423265236927938715005838390000000000000)
      constant := (539682331648693540224247261328765528273798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree061.table
  base := (-7794382850288721612665846475536648598001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-10435557969714878568390226364190000000000000)
      constant := (91578443914568718077205866945607542775888555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11623033662650944443/5000000000000000000)
  centralHi := (232460673253018888861/100000000000000000000)
  directionLo := (234389840549317022427/100000000000000000000)
  directionHi := (58597460137329255607/25000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree062.table
  base := (-1954109559287663827422021183191065082539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-64519409624619855625482502230000000000000)
      constant := (560790017059833017827396316665121657028596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree062.table
  base := (-7818224329757640586789403627727023916291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-10615691030758916914011891455230000000000000)
      constant := (95135088394464012918360041076946450440959505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234389840549317022427/100000000000000000000)
  centralHi := (58597460137329255607/25000000000000000000)
  directionLo := (118151629375372671107/50000000000000000000)
  directionHi := (47260651750149068443/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree063.table
  base := (-7837941063310914003389820766208493858623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-7290617112479085837328796230000000000000)
      constant := (64698405803393995660480107823791506141377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree063.table
  base := (-7839572395040391310466397885478019925601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-10795824091802955259633556546270000000000000)
      constant := (98756793019861581022856890210046261207506555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118151629375372671107/50000000000000000000)
  centralHi := (47260651750149068443/20000000000000000000)
  directionLo := (119100653692275291399/50000000000000000000)
  directionHi := (238201307384550582799/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree064.table
  base := (-7856949824461908466826385913071257961069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-66711698400003689446435829910000000000000)
      constant := (604169115448906254437124383422358678350379) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree064.table
  base := (-3929219715263115540457263892573108822813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-10975957152846993605255221637310000000000000)
      constant := (102443539895318945596216839959871715502070430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119100653692275291399/50000000000000000000)
  centralHi := (238201307384550582799/100000000000000000000)
  directionLo := (120042175487614142607/50000000000000000000)
  directionHi := (48016870195045657043/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree065.table
  base := (-7873476710074458050763104397239920877733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-67807842787695606356912493750000000000000)
      constant := (626440297009676524148918637674840712100403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree065.table
  base := (-7874836571971708691051873170849064451707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-11156090213891031950876886728350000000000000)
      constant := (106195312929667893632673264951673101867283385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120042175487614142607/50000000000000000000)
  centralHi := (48016870195045657043/20000000000000000000)
  directionLo := (241952739861907837257/100000000000000000000)
  directionHi := (120976369930953918629/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree066.table
  base := (-3943766354240095031385489488625479011021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-7655998575043058140821017510000000000000)
      constant := (72122122001985791590173856482749041977958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree066.table
  base := (-7888773833804507414917345565787694287243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-11336223274935070296498551819390000000000000)
      constant := (110012097652060422801239938034424781754933865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241952739861907837257/100000000000000000000)
  centralHi := (120976369930953918629/50000000000000000000)
  directionLo := (60951702739839174129/25000000000000000000)
  directionHi := (243806810959356696517/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree067.table
  base := (-3949563863264123918404664234509763147089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-70000131563079440177865821430000000000000)
      constant := (672145429311850764919428726088824263352398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree067.table
  base := (-7900260223413091739162658181358527302441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-11516356335979108642120216910430000000000000)
      constant := (113893881046820201918705133617658928047972755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60951702739839174129/25000000000000000000)
  centralHi := (243806810959356696517/100000000000000000000)
  directionLo := (245646888467285372691/100000000000000000000)
  directionHi := (61411722116821343173/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree068.table
  base := (-3954135348644891328356901641908056873893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-71096275950771357088342485270000000000000)
      constant := (695579210493972084417989837205654976269926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree068.table
  base := (-1977325960938500408233886055898077935589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (-688028788060185116925993058910000000000000)
      constant := (6931803023833825337038257483450653501899740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245646888467285372691/100000000000000000000)
  centralHi := (61411722116821343173/25000000000000000000)
  directionLo := (247473284532182152663/100000000000000000000)
  directionHi := (30934160566522769083/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree069.table
  base := (-79149696770054926496900096583350797591/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-8021380037607030444313238790000000000000)
      constant := (79933374339785533295821953951664920240900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree069.table
  base := (-1978977996368041420092798164176785516877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-11876622458067185333363547092510000000000000)
      constant := (121852398192142987430000320784136179712450940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247473284532182152663/100000000000000000000)
  centralHi := (30934160566522769083/12500000000000000000)
  directionLo := (31160787483187963281/12500000000000000000)
  directionHi := (249286299865503706249/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree070.table
  base := (-7919231932351749865386768826686620548171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-73288564726155190909295812950000000000000)
      constant := (743608839604056562205812580059820415066461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree070.table
  base := (-1980022802401791363247593233678129477373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-12056755519111223678985212183550000000000000)
      constant := (125929111927021876648907452453040411620784060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31160787483187963281/12500000000000000000)
  centralHi := (249286299865503706249/100000000000000000000)
  directionLo := (125543112160844252357/50000000000000000000)
  directionHi := (50217244864337700943/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree071.table
  base := (-7921064018993181025827564652139260668713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-74384709113847107819772476790000000000000)
      constant := (768204563130950731550023465920746653981583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree071.table
  base := (-7921847421848518831595681196936367531003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-12236888580155262024606877274590000000000000)
      constant := (130070784076090345048612020804044948917700665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125543112160844252357/50000000000000000000)
  centralHi := (50217244864337700943/20000000000000000000)
  directionLo := (252873337439139136431/100000000000000000000)
  directionHi := (15804583589946196027/6250000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree072.table
  base := (-7920471852292708431283721904939369161669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-8386761500171002747805460070000000000000)
      constant := (88131942933387334110287591135060630838331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree072.table
  base := (-7921185939204457416720781836943606605017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-12417021641199300370228542365630000000000000)
      constant := (134277406956271497966342880788448488455750435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252873337439139136431/100000000000000000000)
  centralHi := (15804583589946196027/6250000000000000000)
  directionLo := (254647908947032537229/100000000000000000000)
  directionHi := (25464790894703253723/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree073.table
  base := (-7917460770962916841182816258545688442057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-76576997889230941640725804470000000000000)
      constant := (818557561364249125698658961883088804021487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree073.table
  base := (-989763943732523617326026416933957597401/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-12597154702243338715850207456670000000000000)
      constant := (138548973648637710231899567191585450174044440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254647908947032537229/100000000000000000000)
  centralHi := (25464790894703253723/10000000000000000000)
  directionLo := (256410199240559891931/100000000000000000000)
  directionHi := (64102549810139972983/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree074.table
  base := (-7912035594364206744328515125919365472321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-77673142276922858551202468310000000000000)
      constant := (844314744647996483269002384206725710749111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree074.table
  base := (-7912628566922218482963152298709066593669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-12777287763287377061471872547710000000000000)
      constant := (142885477920750081996438091147513398772148295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256410199240559891931/100000000000000000000)
  centralHi := (64102549810139972983/25000000000000000000)
  directionLo := (129080229913483524363/50000000000000000000)
  directionHi := (258160459826967048727/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree075.table
  base := (-7904200674084643231444215669563554345111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-8752142962734975051297681350000000000000)
      constant := (96717666343048388209678668080436445654889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree075.table
  base := (-1580948175334804006755962643028987108463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-12957420824331415407093537638750000000000000)
      constant := (147286914156928993353086821390365568141354825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129080229913483524363/50000000000000000000)
  centralHi := (258160459826967048727/100000000000000000000)
  directionLo := (129949466872279351317/50000000000000000000)
  directionHi := (51979786748911740527/20000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree076.table
  base := (-3946979970186461119289853785231993041231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-79865431052306692372155795990000000000000)
      constant := (896990283310327894128527740305824125257842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree076.table
  base := (-1973612995476091723193589289246562683057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-13137553885375453752715202729790000000000000)
      constant := (151753277295644666880865902280802867691930540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129949466872279351317/50000000000000000000)
  centralHi := (51979786748911740527/20000000000000000000)
  directionLo := (13081292797832135631/5000000000000000000)
  directionHi := (261625855956642712621/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree077.table
  base := (-1576263388787748505824664203562999302703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-80961575439998609282632459830000000000000)
      constant := (923908571360286395122766595249665031378365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree077.table
  base := (-7881765040812197070592864204695115004281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-13317686946419492098336867820830000000000000)
      constant := (156284562773299637154391748102557558818813955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13081292797832135631/5000000000000000000)
  centralHi := (261625855956642712621/100000000000000000000)
  directionLo := (13167072686111120577/5000000000000000000)
  directionHi := (263341453722222411541/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree078.table
  base := (-3933137446791727410213187447548274369629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-9117524425298947354789902630000000000000)
      constant := (105690425817566537823740300844903451260742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree078.table
  base := (-314667316077613447064632976020947064547/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-13497820007463530443958532911870000000000000)
      constant := (160880766473749521168109550744575287293239625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13167072686111120577/5000000000000000000)
  centralHi := (263341453722222411541/100000000000000000000)
  directionLo := (132522973472546312757/50000000000000000000)
  directionHi := (53009189389018525103/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree079.table
  base := (-7848836690077585857468463251276293371253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-83153864215382443103585787510000000000000)
      constant := (978906040196830489296399730928513359658723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree079.table
  base := (-7849208135544123253234425885188931676611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-13677953068507568789580198002910000000000000)
      constant := (165541884682975354005764043343519993727297105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132522973472546312757/50000000000000000000)
  centralHi := (53009189389018525103/20000000000000000000)
  directionLo := (266739548502857561773/100000000000000000000)
  directionHi := (133369774251428780887/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree080.table
  base := (-3914502478330094864199613543852103985409/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-84250008603074360014062451350000000000000)
      constant := (1006985171267329854977630896210662128262638) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree080.table
  base := (-7829343061759443939376771072654605690983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-13858086129551607135201863093950000000000000)
      constant := (170267914048380780919104117911214094776529565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266739548502857561773/100000000000000000000)
  centralHi := (133369774251428780887/50000000000000000000)
  directionLo := (268422464557264186859/100000000000000000000)
  directionHi := (13421123227863209343/5000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree081.table
  base := (-390339103324874895476285740234646809507/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-9482905887862919658282123910000000000000)
      constant := (115050133801233428241176974205307063809860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree081.table
  base := (-7807089775897385340075393196993133147709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-14038219190595645480823528184990000000000000)
      constant := (175058851542241281041357763924422922601560495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268422464557264186859/100000000000000000000)
  centralHi := (13421123227863209343/5000000000000000000)
  directionLo := (54018978969426364173/20000000000000000000)
  directionHi := (135047447423565910433/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree082.table
  base := (-7782170167404606589642032259058462957707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-86442297378458193835015779030000000000000)
      constant := (1064304119697807621176138393128473833380637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree082.table
  base := (-7782450171159252810902923641798709516021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-14218352251639683826445193276030000000000000)
      constant := (179914694428880968133722529033852864749349655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54018978969426364173/20000000000000000000)
  centralHi := (135047447423565910433/50000000000000000000)
  directionLo := (271757032965056200211/100000000000000000000)
  directionHi := (67939258241264050053/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree083.table
  base := (-7755171204103579755870701633542781078037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-87538441766150110745492442870000000000000)
      constant := (1093543900224951580110165072408114970297667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree083.table
  base := (-484714122439727496405204074759553552071/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-14398485312683722172066858367070000000000000)
      constant := (184835440235195934457746873709281121876118480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271757032965056200211/100000000000000000000)
  centralHi := (67939258241264050053/25000000000000000000)
  directionLo := (136704533309486566889/50000000000000000000)
  directionHi := (273409066618973133779/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree084.table
  base := (-309031477530560876892564026058495970771/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-9848287350426891961774345190000000000000)
      constant := (124796725548611810038416822908537600730725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree084.table
  base := (-386300934381313438891429831916518087747/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-14578618373727760517688523458110000000000000)
      constant := (189821086724182081661278199616100627264111700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136704533309486566889/50000000000000000000)
  centralHi := (273409066618973133779/100000000000000000000)
  directionLo := (55010235575916428177/20000000000000000000)
  directionHi := (137525588939791070443/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree085.table
  base := (-1923504741636895411867837253006969039673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-89730730541533944566445770550000000000000)
      constant := (1153183994465516914856405317141749114571772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree085.table
  base := (-7694229758093103047781869181627785562039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (-868161849104223462547658149950000000000000)
      constant := (11463037168891786597249908367711638227226685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55010235575916428177/20000000000000000000)
  centralHi := (137525588939791070443/50000000000000000000)
  directionLo := (276683543414553267623/100000000000000000000)
  directionHi := (34585442926819158453/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree086.table
  base := (-76598687368557129146270077082162344279/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-90826874929225861476922434390000000000000)
      constant := (1183584280777870367792565756366053890148900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree086.table
  base := (-119688444366210945655296175049484196327/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-14938884495815837208931853640190000000000000)
      constant := (199987073842423843956591566029331701523679040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276683543414553267623/100000000000000000000)
  centralHi := (34585442926819158453/12500000000000000000)
  directionLo := (17394145919398117393/6250000000000000000)
  directionHi := (278306334710369878289/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree087.table
  base := (-7623337562960100182757254958138708074657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-10213668812990864265266566470000000000000)
      constant := (134930153005624609891494124431861291925343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree087.table
  base := (-7623511881772657913207857369904523185839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-15119017556859875554553518731230000000000000)
      constant := (205167410976058927821155507097049963996462645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17394145919398117393/6250000000000000000)
  centralHi := (278306334710369878289/100000000000000000000)
  directionLo := (34989964785324492687/12500000000000000000)
  directionHi := (279919718282595941497/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree088.table
  base := (-1896106659419305798828817108223449727917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-93019163704609695297875762070000000000000)
      constant := (1245545272548421960857970808663955809794988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree088.table
  base := (-758458512824508556395786360861978623989/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-15299150617903913900175183822270000000000000)
      constant := (210412641764718916302216644400056408883358950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34989964785324492687/12500000000000000000)
  centralHi := (279919718282595941497/100000000000000000000)
  directionLo := (281523855875297579443/100000000000000000000)
  directionHi := (70380963968824394861/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree089.table
  base := (-47144606529577502093912074188560304563/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-94115308092301612208352425910000000000000)
      constant := (1277105957517743917851612869058473161429280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree089.table
  base := (-150865622514862501854851364500326869587/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-15479283678947952245796848913310000000000000)
      constant := (215722764840150155760965034166609383672339250) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281523855875297579443/100000000000000000000)
  centralHi := (70380963968824394861/25000000000000000000)
  directionLo := (11324756186011795657/4000000000000000000)
  directionHi := (141559452325147445713/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree090.table
  base := (-468716860590257826545869012672839687089/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-10579050275554836568758787750000000000000)
      constant := (145450380343413435266530152297234565006576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree090.table
  base := (-1499920146903281582296205510541509899539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-15659416739991990591418514004350000000000000)
      constant := (221097778959291928807177639994637590975830725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11324756186011795657/4000000000000000000)
  centralHi := (141559452325147445713/50000000000000000000)
  directionLo := (28470501736687082339/10000000000000000000)
  directionHi := (284705017366870823391/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree091.table
  base := (-931678213543304888683787494418353903273/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-96307596867685446029305753590000000000000)
      constant := (1341387661198546588294166282791878518964344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree091.table
  base := (-7453544736817481418467996583035403539939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-15839549801036028937040179095390000000000000)
      constant := (226537682991789304450318540921651841884788145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28470501736687082339/10000000000000000000)
  centralHi := (284705017366870823391/100000000000000000000)
  directionLo := (8946323204766209639/3125000000000000000)
  directionHi := (286282342552518708449/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree092.table
  base := (-3702502838927658076551420944862120307297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-97403741255377362939782417430000000000000)
      constant := (1374108664493477163062988100552481834468654) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree092.table
  base := (-1851278461166363740515801659339051698263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-16019682862080067282661844186430000000000000)
      constant := (232042475908774669682007925188292281184039860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8946323204766209639/3125000000000000000)
  centralHi := (286282342552518708449/100000000000000000000)
  directionLo := (287851024665268667633/100000000000000000000)
  directionHi := (143925512332634333817/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree093.table
  base := (-735421042207444949852620792548736928951/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-10944431738118808872251009030000000000000)
      constant := (156357380697619933713242746964512630710490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree093.table
  base := (-7354308706821306703653293322706683210411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-16199815923124105628283509277470000000000000)
      constant := (237612156772788411059042104342390842760956105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287851024665268667633/100000000000000000000)
  centralHi := (143925512332634333817/50000000000000000000)
  directionLo := (289411204248094993697/100000000000000000000)
  directionHi := (144705602124047496849/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree094.table
  base := (-7301040619826295190219078709404768455839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-99596030030761196760735745110000000000000)
      constant := (1440710940444451204962448023355357083897449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree094.table
  base := (-7301129915055326210143006926205108802661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-16379948984168143973905174368510000000000000)
      constant := (243246724728722460157243714219061617780154855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289411204248094993697/100000000000000000000)
  centralHi := (144705602124047496849/50000000000000000000)
  directionLo := (18185188629741977271/6250000000000000000)
  directionHi := (290963018075871636337/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree095.table
  base := (-1449099378197130602964477851873400950969/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-100692174418453113671212408950000000000000)
      constant := (1474592201412219369613009587415696957206395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree095.table
  base := (-3622789004889469541742322926972379069037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-16560082045212182319526839459550000000000000)
      constant := (248946178995682306981791683621499824490483070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18185188629741977271/6250000000000000000)
  centralHi := (290963018075871636337/100000000000000000000)
  directionLo := (292506599295310688621/100000000000000000000)
  directionHi := (146253299647655344311/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree096.table
  base := (-1437515960437068546542331044646812660783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-11309813200682781175743230310000000000000)
      constant := (167651133786909835503054419336765936696085) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree096.table
  base := (-7187653485105773233151294351551604152101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-16740215106256220665148504550590000000000000)
      constant := (254710518859673759203497405814775932000214055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292506599295310688621/100000000000000000000)
  centralHi := (146253299647655344311/50000000000000000000)
  directionLo := (18377629847393068317/6250000000000000000)
  directionHi := (294042077558289093073/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree097.table
  base := (-7127289871956585327005888130867298410761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-102884463193836947492165736630000000000000)
      constant := (1543514943787577665857817479432194314303151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree097.table
  base := (-356367839670009769024804317014583558157/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-16920348167300259010770169641630000000000000)
      constant := (260539743667030306910005602282660535169262700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18377629847393068317/6250000000000000000)
  centralHi := (294042077558289093073/100000000000000000000)
  directionLo := (147784789574470708751/50000000000000000000)
  directionHi := (295569579148941417503/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree098.table
  base := (-7064627575360444632525402721729716000481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-103980607581528864402642400470000000000000)
      constant := (1578556416252837234090609870964432555995671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree098.table
  base := (-7064688349365593729185746631980416181263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-17100481228344297356391834732670000000000000)
      constant := (266433852818505554147017855672080298618074965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147784789574470708751/50000000000000000000)
  centralHi := (295569579148941417503/100000000000000000000)
  directionLo := (148544613552435646717/50000000000000000000)
  directionHi := (59417845420974258687/20000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree099.table
  base := (-6999593348161055585519503314467410741829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-11675194663246753479235451590000000000000)
      constant := (179331624172898889977735912195532589258171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree099.table
  base := (-1399929706743867806489077952527527885509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-17280614289388335702013499823710000000000000)
      constant := (272392845763962900176123875478486611027197475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148544613552435646717/50000000000000000000)
  centralHi := (59417845420974258687/20000000000000000000)
  directionLo := (59720228266562156157/20000000000000000000)
  directionHi := (149300570666405390393/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree100.table
  base := (-6932187590586298857845614792274750037967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-106172896356912698223595728150000000000000)
      constant := (1649799544095285066938140671869527249658297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree100.table
  base := (-3466118848248279613720231716041138861421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-17460747350432374047635164914750000000000000)
      constant := (278416721997601585128119589775641108690493310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59720228266562156157/20000000000000000000)
  centralHi := (149300570666405390393/50000000000000000000)
  directionLo := (300105438719035356517/100000000000000000000)
  directionHi := (150052719359517678259/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree101.table
  base := (-686241067071702155711375489211688723871/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-107269040744604615134072391990000000000000)
      constant := (1686001192557694781537672097660948014851610) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree101.table
  base := (-3431228080010278228460665856397382075479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-17640880411476412393256830005790000000000000)
      constant := (284505481053664437406730722478809565801865690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300105438719035356517/100000000000000000000)
  centralHi := (150052719359517678259/50000000000000000000)
  directionLo := (37700279154352784071/12500000000000000000)
  directionHi := (301602233234822272569/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree102.table
  base := (-848782865942724920154427196540742147527/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-12040576125810725782727672870000000000000)
      constant := (191398839988046885833001560167674062819784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree102.table
  base := (-3395152110786914724389989473846769863209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (-1048294910148261808169323240990000000000000)
      constant := (17097595441328132138244315071322049123254470) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37700279154352784071/12500000000000000000)
  centralHi := (301602233234822272569/100000000000000000000)
  directionLo := (303091636037221554079/100000000000000000000)
  directionHi := (1894322725232634713/625000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree103.table
  base := (-6715744673710541347417357954916168260741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-109461329519988448955025719670000000000000)
      constant := (1759564643285617458121305707315754485653331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree103.table
  base := (-6715782155800193803643066052466801622943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-18001146533564489084500160187870000000000000)
      constant := (296877645947482698415481965953467471654847365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303091636037221554079/100000000000000000000)
  centralHi := (1894322725232634713/625000000000000000)
  directionLo := (304573755565391789879/100000000000000000000)
  directionHi := (7614343889134794747/2500000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree104.table
  base := (-66388561980169138628296813288073510851/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-110557473907680365865502383510000000000000)
      constant := (1796926440138138241286016147480733840234100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree104.table
  base := (-1327778043373075457834701131016393018549/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-18181279594608527430121825278910000000000000)
      constant := (303161051021108316978443642954374560440983475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304573755565391789879/100000000000000000000)
  centralHi := (7614343889134794747/2500000000000000000)
  directionLo := (15302434881636849589/5000000000000000000)
  directionHi := (306048697632736991781/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree105.table
  base := (-819949720954570894740110239618376378317/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-12405957588374698086219894150000000000000)
      constant := (203852772005044829970789879333052988973464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree105.table
  base := (-204988395012520951176165360051211356219/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-18361412655652565775743490369950000000000000)
      constant := (309509337382967887219914026223181986888433440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15302434881636849589/5000000000000000000)
  centralHi := (306048697632736991781/100000000000000000000)
  directionLo := (19219785344691629127/6250000000000000000)
  directionHi := (307516565515066066033/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree106.table
  base := (-6477969630145454944721826170078919919347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-112749762683064199686455711190000000000000)
      constant := (1872810164779229560066306208809289720725877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree106.table
  base := (-3238998822625850993619476837897147789337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-18541545716696604121365155460990000000000000)
      constant := (315922504716829475613187569875705242888816070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19219785344691629127/6250000000000000000)
  centralHi := (307516565515066066033/100000000000000000000)
  directionLo := (308977460034982757107/100000000000000000000)
  directionHi := (77244365008745689277/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree107.table
  base := (-6393972015340112653629913930639382169293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-113845907070756116596932375030000000000000)
      constant := (1911332088271447693400031433334245560476363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree107.table
  base := (-639399743505215473054015078131194402973/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-18721678777740642466986820552030000000000000)
      constant := (322400552728442410523012677142806240877040150) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308977460034982757107/100000000000000000000)
  centralHi := (77244365008745689277/25000000000000000000)
  directionLo := (310431479642701206721/100000000000000000000)
  directionHi := (155215739821350603361/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree108.table
  base := (-3153802568439789017281860976070443062047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-12771339050938670389712115430000000000000)
      constant := (216693412955458503332113044087859113875906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree108.table
  base := (-6307628199640213862731533457238267235347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-18901811838784680812608485643070000000000000)
      constant := (328943481143490514342338857879962703844923585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310431479642701206721/100000000000000000000)
  centralHi := (155215739821350603361/50000000000000000000)
  directionLo := (311878720493470443161/100000000000000000000)
  directionHi := (155939360246735221581/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree109.table
  base := (-388679324610417103977174317799600125089/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-116038195846139950417885702710000000000000)
      constant := (1989536047971240666648260249526857581987184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree109.table
  base := (-6218890116333723374607931251832241923211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-19081944899828719158230150734110000000000000)
      constant := (335551289705749502504467583389940410420960105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311878720493470443161/100000000000000000000)
  centralHi := (155939360246735221581/50000000000000000000)
  directionLo := (31331927652178010773/10000000000000000000)
  directionHi := (313319276521780107731/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree110.table
  base := (-6127764371684603077586355634075381214581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-117134340233831867328362366550000000000000)
      constant := (2029218080716641271547070828793321569068771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree110.table
  base := (-3063891675539197619552794757457022436181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-19262077960872757503851815825150000000000000)
      constant := (342223978175427821208505979142249205159436910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31331927652178010773/10000000000000000000)
  centralHi := (313319276521780107731/100000000000000000000)
  directionLo := (314753239512509472599/100000000000000000000)
  directionHi := (1573766197562547363/500000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree111.table
  base := (-6034290844203221047548305917133248163447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-13136720513502642693204336710000000000000)
      constant := (229920757030355516860586686192866751836553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree111.table
  base := (-3017154029740976045971372009911049473067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-19442211021916795849473480916190000000000000)
      constant := (348961546327672311245841194444415067022836370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314753239512509472599/100000000000000000000)
  centralHi := (1573766197562547363/500000000000000000)
  directionLo := (19761293698073265587/6250000000000000000)
  directionHi := (316180699169172249393/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree112.table
  base := (-371153048366744141542039650343283903313/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-119326629009215701149315694230000000000000)
      constant := (2109742244178007399022520340110567117922928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree112.table
  base := (-5938464387745769746461178565420459851837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-19622344082960834195095146007230000000000000)
      constant := (355763993951221984566194351707079435514095535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19761293698073265587/6250000000000000000)
  centralHi := (316180699169172249393/100000000000000000000)
  directionLo := (39700217897425097133/12500000000000000000)
  directionHi := (63520348635880155413/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree113.table
  base := (-365014894573917221995066258798413119401/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-120422773396907618059792358070000000000000)
      constant := (2150584372058528361972135850543028510806256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree113.table
  base := (-5840252473504405896243006647191226583899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-19802477144004872540716811098270000000000000)
      constant := (362631320847194905302339296929270677586265945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39700217897425097133/12500000000000000000)
  centralHi := (63520348635880155413/20000000000000000000)
  directionLo := (63803291455560972453/20000000000000000000)
  directionHi := (159508228638902431133/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree114.table
  base := (-5739659605498018336378185249945033006599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-13502101976066614996696557990000000000000)
      constant := (243534799513845348416707254210054966993401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree114.table
  base := (-358729527911396374968526392840444746519/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-19982610205048910886338476189310000000000000)
      constant := (369563526827994697747165189751636917460480720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63803291455560972453/20000000000000000000)
  centralHi := (159508228638902431133/50000000000000000000)
  directionLo := (64084985061266556163/20000000000000000000)
  directionHi := (20026557831645798801/6250000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree115.table
  base := (-704589098226610705310847386689322724429/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-122615062172291451880745685750000000000000)
      constant := (2233428713661256161137223727908368763841112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree115.table
  base := (-2818362214838157133079639664103579986729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-20162743266092949231960141280350000000000000)
      constant := (376560611716324578077311831363790653838353190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64084985061266556163/20000000000000000000)
  centralHi := (20026557831645798801/6250000000000000000)
  directionLo := (80456807318063673503/25000000000000000000)
  directionHi := (321827229272254694013/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree116.table
  base := (-5531397981499327713304763756560249422751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-123711206559983368791222349590000000000000)
      constant := (2275430925022123985945189871830957755195241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree116.table
  base := (-5531408538970755804751438329029120892331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-20342876327136987577581806371390000000000000)
      constant := (383622575344298040450968023265840920310581705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80456807318063673503/25000000000000000000)
  centralHi := (321827229272254694013/100000000000000000000)
  directionLo := (323223449403881950843/100000000000000000000)
  directionHi := (80805862350970487711/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree117.table
  base := (-5423715312957428106958753195077135866041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-13867483438630587300188779270000000000000)
      constant := (257535536513734539794569354894922864133959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree117.table
  base := (-2711862442346552693483153141441036049553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-20523009388181025923203471462430000000000000)
      constant := (390749417552636435843036792350057405816791830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323223449403881950843/100000000000000000000)
  centralHi := (80805862350970487711/25000000000000000000)
  directionLo := (6492273284082588041/2000000000000000000)
  directionHi := (324613664204129402051/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree118.table
  base := (-5313664894207420364488354477645802607231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-125903495335367202612175677270000000000000)
      constant := (2360595423439534675885670230961187776534921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree118.table
  base := (-1328418392903762506874794652849933808081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-20703142449225064268825136553470000000000000)
      constant := (397941138189944676517283436732179382589291820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6492273284082588041/2000000000000000000)
  centralHi := (324613664204129402051/100000000000000000000)
  directionLo := (325997950502021912877/100000000000000000000)
  directionHi := (162998975251010956439/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree119.table
  base := (-5201246833425187656666871190752521416653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-126999639723059119522652341110000000000000)
      constant := (2403757708496312490611868250273227307250123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree119.table
  base := (-2600627349752575320669154289326165547187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (-1228427971192300153790988332030000000000000)
      constant := (23835161006591599526561760614448551856978210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (325997950502021912877/100000000000000000000)
  centralHi := (162998975251010956439/50000000000000000000)
  directionLo := (8184409587556017471/2500000000000000000)
  directionHi := (327376383502240698841/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree120.table
  base := (-158951913544585268418552101195529293383/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-14232864901194559603681000550000000000000)
      constant := (271922964763177812764069330761743062611744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree120.table
  base := (-5086468363537745237672908273002040712259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-21063408571313140960068466735550000000000000)
      constant := (412519214181447063722557862022712051170785745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8184409587556017471/2500000000000000000)
  centralHi := (327376383502240698841/100000000000000000000)
  directionLo := (3287490368327998963/1000000000000000000)
  directionHi := (328749036832799896301/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree121.table
  base := (-77645440501665886528408208251401160817/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-129191928498442953343605668790000000000000)
      constant := (2491242345675346986503592966337192931369408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree121.table
  base := (-4969314654662525981383243688178952105123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-21243541632357179305690131826590000000000000)
      constant := (419905569266691986652055247102499414208097265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3287490368327998963/1000000000000000000)
  centralHi := (328749036832799896301/100000000000000000000)
  directionLo := (330115982590938892169/100000000000000000000)
  directionHi := (33011598259093889217/10000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree122.table
  base := (-242489390141749066532813626626795756209/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-130288072886134870254082332630000000000000)
      constant := (2535564696076221342434330975067176763882380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree122.table
  base := (-4849793659938739203382323857877222324249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-21423674693401217651311796917630000000000000)
      constant := (427356802241991349791872787631299413741460195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330115982590938892169/100000000000000000000)
  centralHi := (33011598259093889217/10000000000000000000)
  directionLo := (20717330711706959497/6250000000000000000)
  directionHi := (331477291387311351953/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree123.table
  base := (-4727900154817086275922940574646504348921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-14598246363758531907173221830000000000000)
      constant := (286697081474264000832967168615353495651079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree123.table
  base := (-590988182854694483311691814948622279357/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-21603807754445255996933462008670000000000000)
      constant := (434872912986729311100730691218435926450633080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20717330711706959497/6250000000000000000)
  centralHi := (331477291387311351953/100000000000000000000)
  directionLo := (8320825809713689539/2500000000000000000)
  directionHi := (332833032388547581561/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree124.table
  base := (-575455666677397427408633646547250846033/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-132480361661518704075035660310000000000000)
      constant := (2625369456483514751079855136288597939085624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree124.table
  base := (-920730028703159884607153815089344405019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-21783940815489294342555127099710000000000000)
      constant := (442453901385079260690028156897827486673737725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8320825809713689539/2500000000000000000)
  centralHi := (332833032388547581561/100000000000000000000)
  directionLo := (41772909169782852053/12500000000000000000)
  directionHi := (13367330934330512657/4000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree125.table
  base := (-447702342046391906686656773400025012113/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-133576506049210620985512324150000000000000)
      constant := (2670851864985233648428235646643997748909830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree125.table
  base := (-895405555812778848177571942005402366679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-21964073876533332688176792190750000000000000)
      constant := (450099767325645535348180272162760967900744225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41772909169782852053/12500000000000000000)
  centralHi := (13367330934330512657/4000000000000000000)
  directionLo := (167764040348290116787/50000000000000000000)
  directionHi := (13421123227863209343/4000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree126.table
  base := (-4348034494498356345521712401507222261841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-14963627826322504210665443110000000000000)
      constant := (301857884229623248822287729258492777738159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree126.table
  base := (-4348038443730607062372322604349991163797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-22144206937577371033798457281790000000000000)
      constant := (457810510701138667132531001131662262768313335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167764040348290116787/50000000000000000000)
  centralHi := (13421123227863209343/4000000000000000000)
  directionLo := (336867519478233911871/100000000000000000000)
  directionHi := (5263554991847404873/1562500000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree127.table
  base := (-2108339315518578138378324496403339746087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-135768794824594454806465651830000000000000)
      constant := (2762976735048009538803217573974739884570434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree127.table
  base := (-4216682209126892915992873932046235708761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-22324339998621409379420122372830000000000000)
      constant := (465586131408080826026892473933635189400840355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336867519478233911871/100000000000000000000)
  centralHi := (5263554991847404873/1562500000000000000)
  directionLo := (338201653489313607279/100000000000000000000)
  directionHi := (4227520668616420091/1250000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree128.table
  base := (-408295590278347423566749119998917553903/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-136864939212286371716942315670000000000000)
      constant := (2809619195275106148260254655360097420148730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree128.table
  base := (-1020739786102730622885703027356488795463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-22504473059665447725041787463870000000000000)
      constant := (473426629346538455384513374357111494762223860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338201653489313607279/100000000000000000000)
  centralHi := (4227520668616420091/1250000000000000000)
  directionLo := (339530545262710049639/100000000000000000000)
  directionHi := (8488263631567751241/2500000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree129.table
  base := (-1973433189914832401789347715091575872057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-15329009288886476514157664390000000000000)
      constant := (317405370901896430726642299979816848255886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree129.table
  base := (-3946869316456157491597059298587522420813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-22684606120709486070663452554910000000000000)
      constant := (481332004419879403045172939877859030101925215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell011.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339530545262710049639/100000000000000000000)
  centralHi := (8488263631567751241/2500000000000000000)
  directionLo := (170427128056158245957/50000000000000000000)
  directionHi := (68170851222463298383/20000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree130.table
  base := (-29753204139373314485676219824783324873/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-139057227987670205537895643350000000000000)
      constant := (2904064162964918217178709057261849609746304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree130.table
  base := (-3808412790004151442382553010142461504857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-22864739181753524416285117645950000000000000)
      constant := (489302256534552124163473245793044143125481635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170427128056158245957/50000000000000000000)
  centralHi := (68170851222463298383/20000000000000000000)
  directionLo := (342172846166039439929/100000000000000000000)
  directionHi := (34217284616603943993/10000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree131.table
  base := (-3667587218215653649587232282768535999281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-140153372375362122448372307190000000000000)
      constant := (2951866669230040780617634297045083176006471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree131.table
  base := (-733517925560716738089823027523012907587/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-23044872242797562761906782736990000000000000)
      constant := (497337385599884777083649799466524231742683925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342172846166039439929/100000000000000000000)
  centralHi := (34217284616603943993/10000000000000000000)
  directionLo := (343486374397668849223/100000000000000000000)
  directionHi := (42935796799708606153/12500000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree132.table
  base := (-1762198854124037309008424241465757989873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-15694390751450448817649885670000000000000)
      constant := (333339539593646483578107921957068484020254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree132.table
  base := (-352439989073688185835750496313854707497/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-23225005303841601107528447828030000000000000)
      constant := (505437391527902253891102303735616799476668350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (343486374397668849223/100000000000000000000)
  centralHi := (42935796799708606153/12500000000000000000)
  directionLo := (172397449328827792521/50000000000000000000)
  directionHi := (344794898657655585043/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree133.table
  base := (-844710415313658100984087482048680369331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-142345661150745956269325634870000000000000)
      constant := (3048631723751392664734391552256247506704084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree133.table
  base := (-844710909483912778684390017413993634581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-23405138364885639453150112919070000000000000)
      constant := (513602274233159385117160643292969116792121820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172397449328827792521/50000000000000000000)
  centralHi := (344794898657655585043/100000000000000000000)
  directionLo := (3460984757028415923/1000000000000000000)
  directionHi := (346098475702841592301/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree134.table
  base := (-1615459568352689493591152831969638876131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-143441805538437873179802298710000000000000)
      constant := (3097594270920533250393365939564546500229642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree134.table
  base := (-3230920926886005643844149538191510873801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-23585271425929677798771778010110000000000000)
      constant := (521832033632588735765576532316501266787357555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3460984757028415923/1000000000000000000)
  centralHi := (346098475702841592301/100000000000000000000)
  directionLo := (43424645153148250653/12500000000000000000)
  directionHi := (13895886449007440209/4000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree135.table
  base := (-3080630192337561390435824807600484036903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-16059772214014421121142106950000000000000)
      constant := (349660388592289431775084941942399515963097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree135.table
  base := (-616126362704957450480641591748412502719/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-23765404486973716144393443101150000000000000)
      constant := (530126669645361569425630995323667719667855225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43424645153148250653/12500000000000000000)
  centralHi := (13895886449007440209/4000000000000000000)
  directionLo := (34869100987952833329/10000000000000000000)
  directionHi := (348691009879528333291/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree136.table
  base := (-2927974884260445327559784404467518715461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-145634094313821707000755626390000000000000)
      constant := (3196679402476624180056821272599792331560851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree136.table
  base := (-2927976352327556847508712905090847751043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (-1408561032236338499412653423070000000000000)
      constant := (31675657776044747093327837336491277941161345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34869100987952833329/10000000000000000000)
  centralHi := (348691009879528333291/100000000000000000000)
  directionLo := (8749501882760697073/2500000000000000000)
  directionHi := (349980075310427882921/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree137.table
  base := (-2772953267051180818570628958476472685693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-146730238701513623911232290230000000000000)
      constant := (3246801985867396782456388324383711745828763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree137.table
  base := (-2772954596389155410416558590563860905493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-24125670609061792835636773283230000000000000)
      constant := (546910571198064084030488483368297220991562615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8749501882760697073/2500000000000000000)
  centralHi := (349980075310427882921/100000000000000000000)
  directionLo := (351264410178116706179/100000000000000000000)
  directionHi := (17563220508905835309/5000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree138.table
  base := (-2615565393842563168942774739754824891729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-16425153676578393424634328230000000000000)
      constant := (366367916336080837269466209600245175108271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree138.table
  base := (-523113319499510209221897467428848148211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-24305803670105831181258438374270000000000000)
      constant := (555399836586438105845676678612238572129175525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351264410178116706179/100000000000000000000)
  centralHi := (17563220508905835309/5000000000000000000)
  directionLo := (352544066183601601551/100000000000000000000)
  directionHi := (22034004136475100097/6250000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree139.table
  base := (-613952829100864688420982711866339119247/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-148922527476897457732185617910000000000000)
      constant := (3348207185482696641588174576762811791707108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree139.table
  base := (-1227906203100808391012656165527822313147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-24485936731149869526880103465310000000000000)
      constant := (563953978284839644507490180398082593515005170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352544066183601601551/100000000000000000000)
  centralHi := (22034004136475100097/6250000000000000000)
  directionLo := (176909547046474510751/50000000000000000000)
  directionHi := (353819094092949021503/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree140.table
  base := (-2293691085212589435090736110219174129311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-150018671864589374642662281750000000000000)
      constant := (3399489800786995604184654646008027432836201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree140.table
  base := (-286711508984177398806235383341919473213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-24666069792193907872501768556350000000000000)
      constant := (572572996221926063818975936206367410889657720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176909547046474510751/50000000000000000000)
  centralHi := (353819094092949021503/100000000000000000000)
  directionLo := (177544771880392580611/50000000000000000000)
  directionHi := (355089543760785161223/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree141.table
  base := (-133075296845393834031814391890145554713/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-16790535139142365728126549510000000000000)
      constant := (383462121388257478670280392939757671124592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree141.table
  base := (-2129205642765539871716991900322014050389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-24846202853237946218123433647390000000000000)
      constant := (581256890327972383367651616082472689697187895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (177544771880392580611/50000000000000000000)
  centralHi := (355089543760785161223/100000000000000000000)
  directionLo := (89088866038260501757/25000000000000000000)
  directionHi := (356355464153042007029/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree142.table
  base := (-24529404468011030293942818616795644693/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-152210960639973208463615609430000000000000)
      constant := (3503215060171795161657591738655907135821040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree142.table
  base := (-981176583031949845033389888354297233189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-25026335914281984563745098738430000000000000)
      constant := (590005660534794947504690216361028080996083790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89088866038260501757/25000000000000000000)
  centralHi := (356355464153042007029/100000000000000000000)
  directionLo := (357616903368978706519/100000000000000000000)
  directionHi := (8940422584224467663/2500000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree143.table
  base := (-896566977974968936952288817422683876597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-153307105027665125374092273270000000000000)
      constant := (3555657703396486718243707349796391690221254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree143.table
  base := (-179313468793650879938313094302292552797/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-25206468975326022909366763829470000000000000)
      constant := (598819306775680981557729524304933872612083350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357616903368978706519/100000000000000000000)
  centralHi := (8940422584224467663/2500000000000000000)
  directionLo := (358873908662506280829/100000000000000000000)
  directionHi := (35887390866250628083/10000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree144.table
  base := (-1621549590997282901641021070818973661057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-17155916601706338031618770790000000000000)
      constant := (400943002417210848993021062289181026338943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree144.table
  base := (-1621550253578523392453280001439679320149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-25386602036370061254988428920510000000000000)
      constant := (607697828985323484828191985914047663382384695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358873908662506280829/100000000000000000000)
  centralHi := (35887390866250628083/10000000000000000000)
  directionLo := (360126526462842427821/100000000000000000000)
  directionHi := (180063263231421213911/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree145.table
  base := (-289519861505153462188243814438019089629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-155499393803048959195045600950000000000000)
      constant := (3661703014842542281500090201600289140966695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree145.table
  base := (-723799953626976135138264208081176370443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-25566735097414099600610094011550000000000000)
      constant := (616641227099760964598633610572595400289419730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360126526462842427821/100000000000000000000)
  centralHi := (180063263231421213911/50000000000000000000)
  directionLo := (361374802394521959709/100000000000000000000)
  directionHi := (36137480239452195971/10000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree146.table
  base := (-635641574761203059445349669844683324637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-156595538190740876105522264790000000000000)
      constant := (3715305682263537504778639523482795700156534) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree146.table
  base := (-31782092308358058055313869054136294043/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-25746868158458137946231759102590000000000000)
      constant := (625649501056321564513929662739738922204314600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361374802394521959709/100000000000000000000)
  centralHi := (36137480239452195971/10000000000000000000)
  directionLo := (362618781296787275441/100000000000000000000)
  directionHi := (181309390648393637721/50000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree147.table
  base := (-1092601160060153975734493633147765406167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-17521298064270310335110992070000000000000)
      constant := (418810558181136302102292471156852234593833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree147.table
  base := (-546300825667290721455623267558664332937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-25927001219502176291853424193630000000000000)
      constant := (634722650793571184866311054984237460077812070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (362618781296787275441/100000000000000000000)
  centralHi := (181309390648393637721/50000000000000000000)
  directionLo := (45482313405297772961/12500000000000000000)
  directionHi := (363858507242382183689/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree148.table
  base := (-911553381336628392527355243994412598153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-158787826966124709926475592470000000000000)
      constant := (3823671038562831366326575572764050286616623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree148.table
  base := (-911553825946489937262604130648656134389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-26107134280546214637475089284670000000000000)
      constant := (643860676251265232015211736734404691885807895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45482313405297772961/12500000000000000000)
  centralHi := (363858507242382183689/100000000000000000000)
  directionLo := (182547011777885681497/50000000000000000000)
  directionHi := (73018804711154272599/20000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree149.table
  base := (-364069927355028618745345086312496164651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-159883971353816626836952256310000000000000)
      constant := (3878433726689127396182476866536375069036282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree149.table
  base := (-728140257069726765308554794926964272027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-26287267341590252983096754375710000000000000)
      constant := (653063577370303669863371123119528536626920985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182547011777885681497/50000000000000000000)
  centralHi := (73018804711154272599/20000000000000000000)
  directionLo := (14653014913232270739/4000000000000000000)
  directionHi := (91581343207701692119/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree150.table
  base := (-542360620732699342134260891736196795339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-17886679526834282638603213350000000000000)
      constant := (437064787516016053222749806608263803204661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree150.table
  base := (-54236098484091477241191067189255831581/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-26467400402634291328718419466750000000000000)
      constant := (662331354092689078399239950591615253233654550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14653014913232270739/4000000000000000000)
  centralHi := (91581343207701692119/25000000000000000000)
  directionLo := (18377629847393068317/5000000000000000000)
  directionHi := (367552596947861366341/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree151.table
  base := (-442769648977453834190201169991507191/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-162076260129200460657905583990000000000000)
      constant := (3989119121069885939545342909766061148224800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree151.table
  base := (-7084320973214981646142551088109276289/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-26647533463678329674340084557790000000000000)
      constant := (671664006361487453169021930529982104788119750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18377629847393068317/5000000000000000000)
  centralHi := (367552596947861366341/100000000000000000000)
  directionLo := (368775737090449695773/100000000000000000000)
  directionHi := (184387868545224847887/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree152.table
  base := (-81852594544713028242012167609161203639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-163172404516892377568382247830000000000000)
      constant := (4045041826615067579014204111143035098334498) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree152.table
  base := (-163705487219394873989350407291340109101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-26827666524722368019961749648830000000000000)
      constant := (681061534120791505489069078460456013542349055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368775737090449695773/100000000000000000000)
  centralHi := (184387868545224847887/50000000000000000000)
  directionLo := (46249354220169239959/12500000000000000000)
  directionHi := (369994833761353919673/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree153.table
  base := (113948950125234721650178894272021219/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-18252060989398254942095434630000000000000)
      constant := (455705689326097081443975837286933637432064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree153.table
  base := (14585330739847693383832988007692607631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1512)
      previous := (783)
      next := (0)
      square := (15528712158968822898419404400000000000000)
      linear := (-1588694093280376845034318514110000000000000)
      constant := (40619055136216838032137548159207307743297270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46249354220169239959/12500000000000000000)
  centralHi := (369994833761353919673/100000000000000000000)
  directionLo := (185604963399136614497/50000000000000000000)
  directionHi := (74241985359654645799/20000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree154.table
  base := (112206302081507022258157523077810192991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-165364693292276211389335575510000000000000)
      constant := (4158047252690729069575779773355400583473838) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree154.table
  base := (44882472019481943577014472667309202613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-27187932646810444711205079830910000000000000)
      constant := (700051215892216659526725714127689308988878925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185604963399136614497/50000000000000000000)
  centralHi := (74241985359654645799/20000000000000000000)
  directionLo := (372421055389013707709/100000000000000000000)
  directionHi := (37242105538901370771/10000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree155.table
  base := (422019792753567590536950107493773872471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-166460837679968128299812239350000000000000)
      constant := (4215129972550084774771490124717443964852239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree155.table
  base := (16880782877517076786350587650967632717/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-27368065707854483056826744921950000000000000)
      constant := (709643369797357282796658834352341205731901625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372421055389013707709/100000000000000000000)
  centralHi := (37242105538901370771/10000000000000000000)
  directionLo := (186814129043117522223/50000000000000000000)
  directionHi := (373628258086235044447/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree156.table
  base := (310996230350585493273373964138374853459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-18617442451962227245587655910000000000000)
      constant := (474733262576246433435621684688276749706918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree156.table
  base := (310996130464439343859142772618781740933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-27548198768898521402448410012990000000000000)
      constant := (719300398978983544156322368416396279231296370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186814129043117522223/50000000000000000000)
  centralHi := (373628258086235044447/100000000000000000000)
  directionLo := (187415786410884895429/50000000000000000000)
  directionHi := (374831572821769790859/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree157.table
  base := (20608264308240943588219179421786219363/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-168653126455351962120765567030000000000000)
      constant := (4330455424278042769621942413801843038970680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree157.table
  base := (82433039160262340950777819219345805061/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-27728331829942559748070075104030000000000000)
      constant := (729022303385844701475573103340621546883131450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (187415786410884895429/50000000000000000000)
  centralHi := (374831572821769790859/100000000000000000000)
  directionLo := (188015518460265106777/50000000000000000000)
  directionHi := (75206207384106042711/20000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree158.table
  base := (514517046284708626010078343709385431549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-169749270843043879031242230870000000000000)
      constant := (4388698155509933425390366219046768937767882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree158.table
  base := (514516964539270519669745356511811788981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-27908464890986598093691740195070000000000000)
      constant := (738809082967538258788392237601891136070155090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188015518460265106777/50000000000000000000)
  centralHi := (75206207384106042711/20000000000000000000)
  directionLo := (1178833397231303639/312500000000000000)
  directionHi := (377226687114017164481/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree159.table
  base := (1236102986938994210879343177110016687703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-18982823914526199549079877190000000000000)
      constant := (494147506285728470057288046487110016687703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree159.table
  base := (1236102839046267022874820244963315383869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-28088597952030636439313405286110000000000000)
      constant := (748660737674485739313760490063509990729690705) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1178833397231303639/312500000000000000)
  centralHi := (377226687114017164481/100000000000000000000)
  directionLo := (378418559553444802109/100000000000000000000)
  directionHi := (37841855955344480211/10000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree160.table
  base := (289107444305464651136469174517198140469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-171941559618427712852195558550000000000000)
      constant := (4506343627157711776717805184853273916321105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree160.table
  base := (722768543874895481945233095782513615689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-28268731013074674784935070377150000000000000)
      constant := (758577267457909708029135191363611464349341210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (378418559553444802109/100000000000000000000)
  centralHi := (37841855955344480211/10000000000000000000)
  directionLo := (189803344911247215593/50000000000000000000)
  directionHi := (379606689822494431187/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree161.table
  base := (331467352595443143677080131312699607517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-173037704006119629762672222390000000000000)
      constant := (4565746366968185365984610641399071482338265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree161.table
  base := (414334160493088170227148321756008170421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-28448864074118713130556735468190000000000000)
      constant := (768558672269811946472280869543107727225033380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189803344911247215593/50000000000000000000)
  centralHi := (379606689822494431187/100000000000000000000)
  directionLo := (23799444559356886913/6250000000000000000)
  directionHi := (380791112949710190609/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree162.table
  base := (1871501578469603150503839381841153436371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-19348205377090171852572098470000000000000)
      constant := (513948419523067264697738530521841153436371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree162.table
  base := (467875367255518641599172230792489786699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-28628997135162751476178400559230000000000000)
      constant := (778604952062952691500313043883192590967120220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23799444559356886913/6250000000000000000)
  centralHi := (380791112949710190609/100000000000000000000)
  directionLo := (95492965855137201461/25000000000000000000)
  directionHi := (76394372684109761169/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree163.table
  base := (130501977231788074571359324083800192101/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-175229992781503463583625550070000000000000)
      constant := (4685711853085308938372850368978067227662544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree163.table
  base := (2088031536718274806458922968385509631427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-28809130196206789821800065650270000000000000)
      constant := (788716106790830857892152239843679061417412015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95492965855137201461/25000000000000000000)
  centralHi := (76394372684109761169/20000000000000000000)
  directionLo := (47893621898636891613/12500000000000000000)
  directionHi := (76629795037819026581/20000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree164.table
  base := (2306926902907367653047385296564370419307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-176326137169195380494102213910000000000000)
      constant := (4746274598815214238524955721309079333773763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree164.table
  base := (461385362675682221398893943446789337743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-28989263257250828167421730741310000000000000)
      constant := (798892136407665172032822764280211052965193175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47893621898636891613/12500000000000000000)
  centralHi := (76629795037819026581/20000000000000000000)
  directionLo := (384322481689454753907/100000000000000000000)
  directionHi := (96080620422363688477/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree165.table
  base := (2528187348774530311146628511381685941161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-19713586839654144156064319750000000000000)
      constant := (534136001401744349862699528761381685941161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree165.table
  base := (1264093633902804579671103523917864131577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-29169396318294866513043395832350000000000000)
      constant := (809133040868376150546309295726672627340257530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (384322481689454753907/100000000000000000000)
  centralHi := (96080620422363688477/25000000000000000000)
  directionLo := (192746207923417219333/50000000000000000000)
  directionHi := (385492415846834438667/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree166.table
  base := (42997077226584579826863598955578775699/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-178518425944579214315055541590000000000000)
      constant := (4868560094209485512564188605138413374802624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree166.table
  base := (2751812869276734215057365781006700402531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-29349529379338904858665060923390000000000000)
      constant := (819438820128568863721109142719142682081657295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192746207923417219333/50000000000000000000)
  centralHi := (385492415846834438667/100000000000000000000)
  directionLo := (77331762017664172271/20000000000000000000)
  directionHi := (96664702522080215339/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree167.table
  base := (93056364179679186960542606301967616057/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-179614570332271131225532205430000000000000)
      constant := (4930282843323528791351982733924966673424416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree167.table
  base := (1488901793765483935558744090480391473253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-29529662440382943204286726014430000000000000)
      constant := (829809474144516428964854853829410331357701170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77331762017664172271/20000000000000000000)
  centralHi := (96664702522080215339/25000000000000000000)
  directionLo := (387821696353367555073/100000000000000000000)
  directionHi := (193910848176683777537/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree168.table
  base := (200384965789993737218780051339433635567/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (9)
      next := (0)
      square := (182690731281986151746110640000000000000)
      linear := (-20078968302218116459556541030000000000000)
      constant := (554710251076545849654863811461430938169072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree168.table
  base := (641231878551771106831813933249323441879/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-29709795501426981549908391105470000000000000)
      constant := (840245002873144184390136164937278361867575775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell011.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387821696353367555073/100000000000000000000)
  centralHi := (193910848176683777537/50000000000000000000)
  directionLo := (388981106103999699167/100000000000000000000)
  directionHi := (12155659565749990599/3125000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1
  qDenominator := 3
  table := BinomialMassData.Q1_3.Degree169.table
  base := (3436880309739803592672247068729472863361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90000000000000000000000000000000000000000
      center := (162)
      previous := (81)
      next := (0)
      square := (1644216581537875365714995760000000000000)
      linear := (-181806859107654965046485533110000000000000)
      constant := (5054888343040748116598735933108565255770249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_3.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 29
  qDenominator := 85
  table := BinomialMassData.Q29_85.Degree169.table
  base := (859220063897948268026794728505777219667/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (25704)
      previous := (13311)
      next := (0)
      square := (263988106702469989273129874800000000000000)
      linear := (-29889928562471019895530056196510000000000000)
      constant := (850745406272014497026104800281241392329675260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_85.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell011.Kernel169
