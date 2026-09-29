import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell210.Parameters
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch000_049
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch050_099
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch100_149
import ForestUnimodality.BinomialMassData.Q97103_182328.Batch150_199
import ForestUnimodality.BinomialMassData.Q57_107.Batch000_049
import ForestUnimodality.BinomialMassData.Q57_107.Batch050_099
import ForestUnimodality.BinomialMassData.Q57_107.Batch100_149
import ForestUnimodality.BinomialMassData.Q57_107.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree000.table
  base := (87942822701520421958534257/1000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77137536572904627854563308750000000000)
      linear := (-5653413473450754657412265000000000000)
      constant := (109928528376900527448167821250000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree000.table
  base := (87942822701520421958534257/1000000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77137536572904627854563308750000000000)
      linear := (-5653413473450754657412265000000000000)
      constant := (109928528376900527448167821250000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree001.table
  base := (251772615973184702610612470602470811363999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-60819105375967215070711494511597466250000000000)
      constant := (43609961130299145917714722033979330990136683484773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree001.table
  base := (100689744335598004293923901700403499395321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-8045196815790626725141410096940000000000000)
      constant := (5766265214692107302114114021594508322885150645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24946444514091848623/50000000000000000000)
  directionHi := (49892889028183697247/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree002.table
  base := (15084858298986072292015374659325267775457/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-58861404871250130096772216448639156250000000000)
      constant := (13091595847054064316770899541513045043439931898695) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree002.table
  base := (75398439784199252728602917160145624619863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-3893146546180237982425279004500000000000000)
      constant := (865379616614998486187592837704477256272811487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24946444514091848623/50000000000000000000)
  centralHi := (49892889028183697247/100000000000000000000)
  directionLo := (3527960016481658737/5000000000000000000)
  directionHi := (70559200329633174741/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree003.table
  base := (95547313131041447637956813136231455884403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-58208838036344435105459123760986386250000000000)
      constant := (5562000025292130450844685071986199460374766462827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree003.table
  base := (95504987772879431129003804710293438493363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-11549987776825638567130410969530000000000000)
      constant := (1102872681864704737720212391823604577310512987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3527960016481658737/5000000000000000000)
  centralHi := (70559200329633174741/100000000000000000000)
  directionLo := (86417018733209950237/100000000000000000000)
  directionHi := (43208509366604975119/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree004.table
  base := (128686644425472557560905416777936014757463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-463060436951132700878420619337280010000000000000)
      constant := (22782788962500680404313334804674155807126766153101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree004.table
  base := (64311690679094865273572308249996945664943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-15313682461290801169410263930060000000000000)
      constant := (752895900090173827657184751790215030917932407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86417018733209950237/100000000000000000000)
  centralHi := (43208509366604975119/50000000000000000000)
  directionLo := (99785778056367394493/100000000000000000000)
  directionHi := (49892889028183697247/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree005.table
  base := (92024199678172119612817639807503474170989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-576867845684198791124086496108641702500000000000)
      constant := (16711853917591746762724925130649094894957435241503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree005.table
  base := (45989113637732594914535289439109386238707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-19077377145755963771690116890590000000000000)
      constant := (552280951046428715819573295885938363046956443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99785778056367394493/100000000000000000000)
  centralHi := (49892889028183697247/50000000000000000000)
  directionLo := (111563891460872167747/100000000000000000000)
  directionHi := (27890972865218041937/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree006.table
  base := (8668880219639042544379242653029218805007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-28778135600719370057073015536666808125000000000)
      constant := (546819996210773935660690483899953641109540245863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree006.table
  base := (69317444026075924624065030125965592795173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-45682143660442252747939939702240000000000000)
      constant := (867448983377428651487436428072540071911935677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111563891460872167747/100000000000000000000)
  centralHi := (27890972865218041937/25000000000000000000)
  directionLo := (3055302997808883331/2500000000000000000)
  directionHi := (122212119912355333241/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree007.table
  base := (27235219315358937703681864314193202516599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-402241331575165485807709124825682543750000000000)
      constant := (5472672378049971232042880105195399896204096924973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree007.table
  base := (850706871110183663696522483074141138047/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-6651191628671572244062455702912500000000000)
      constant := (90439677880088964852955122415680485116000824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3055302997808883331/2500000000000000000)
  centralHi := (122212119912355333241/100000000000000000000)
  directionLo := (132004176559117144103/100000000000000000000)
  directionHi := (16500522069889643013/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree008.table
  base := (44083255618092757458791995301894309116733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-918290071883397061861084126422726780000000000000)
      constant := (9605625633757907755896840012432010223406671317391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree008.table
  base := (44063662106747726886179247396601528942333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-60736922398302903157059351544360000000000000)
      constant := (635008964700315572470353686660650904860770517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132004176559117144103/100000000000000000000)
  centralHi := (16500522069889643013/12500000000000000000)
  directionLo := (141118400659266349481/100000000000000000000)
  directionHi := (70559200329633174741/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree009.table
  base := (9101594614246105321525803260417892305749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8903894670042152019982118635181557500000000000)
      linear := (-86008123384705262675562500266174039375000000000)
      constant := (732982365379694741626191595844226310537888337341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree009.table
  base := (7278112311323821873304748557613162635899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-68264311767233228361619057465420000000000000)
      constant := (581519778312339570191391035488915495092038255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141118400659266349481/100000000000000000000)
  centralHi := (70559200329633174741/50000000000000000000)
  directionLo := (7483933354227554587/5000000000000000000)
  directionHi := (149678667084551091741/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree010.table
  base := (1903408485683563126036828979029637687707/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-143238111168691155294051984995681270625000000000)
      constant := (1043154992863116376618415726517834483671441420978) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree010.table
  base := (15220671760714721938444677317074323858171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-37895850568081776783089381693240000000000000)
      constant := (275888620269552751939265882824083933852199779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7483933354227554587/5000000000000000000)
  centralHi := (149678667084551091741/100000000000000000000)
  directionLo := (31555033675017069501/20000000000000000000)
  directionHi := (78887584187542673753/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree011.table
  base := (1283306218138307846963061817362203252573/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-314928074520648833149520439184202964375000000000)
      constant := (2039185629737417882475980904337094336972238865355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree011.table
  base := (12827421759921373180386945222838305594127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-41659545252546939385369234653770000000000000)
      constant := (269678289616898846034441137664930760747160023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31555033675017069501/20000000000000000000)
  centralHi := (78887584187542673753/50000000000000000000)
  directionLo := (33095198522664996839/20000000000000000000)
  directionHi := (41368998153331246049/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree012.table
  base := (10853796047785492509597037339409890125119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-228919951135943570473957938918028925000000000000)
      constant := (1362090636555799136904496099260383476076179139671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree012.table
  base := (21697780086041591495134411286893225501539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-90846479874024203975298175228600000000000000)
      constant := (540442054894272432238923956658520538767120011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33095198522664996839/20000000000000000000)
  centralHi := (41368998153331246049/25000000000000000000)
  directionLo := (86417018733209950237/50000000000000000000)
  directionHi := (6913361498656796019/4000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree013.table
  base := (4592657616923633689929316732522027493953/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-371831778887181878272353377569883810625000000000)
      constant := (2089144159467970018313664147566107602831057906331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree013.table
  base := (18362006177592893144379733982209616104397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-98373869242954529179857881149660000000000000)
      constant := (552650592031713321222273353456827894779241253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86417018733209950237/50000000000000000000)
  centralHi := (6913361498656796019/4000000000000000000)
  directionLo := (89945684836075503427/50000000000000000000)
  directionHi := (35978273934430201371/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree014.table
  base := (7758853003615134152500260509527886032303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-800567262140896801667539693525448467500000000000)
      constant := (4342513992707257739315423033012950273183667661781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree014.table
  base := (7755041231061513227259625203529556019203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-52950629305942427192208793535360000000000000)
      constant := (287204323864887364032795996653309886863855147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89945684836075503427/50000000000000000000)
  centralHi := (35978273934430201371/20000000000000000000)
  directionLo := (186682096779796064633/100000000000000000000)
  directionHi := (93341048389898032317/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree015.table
  base := (130528464151261229025517335087440985297/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8903894670042152019982118635181557500000000000)
      linear := (-142911827751238307798395438651854885625000000000)
      constant := (761773409033518154298546661812536129680788611825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree015.table
  base := (13046090869653227851399355802863438263637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-113428647980815179588977292991780000000000000)
      constant := (604618056005269788608395255326933504680380013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186682096779796064633/100000000000000000000)
  centralHi := (93341048389898032317/50000000000000000000)
  directionLo := (1932343283003302117/1000000000000000000)
  directionHi := (193234328300330211701/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree016.table
  base := (1090568380952365838600224968895033639443/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-914374670873962891913205570296810160000000000000)
      constant := (4856575842346431052259156234632387483033577512805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree016.table
  base := (10899694834646236362550364647172260596101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-120956037349745504793536998912840000000000000)
      constant := (642473533519362401976877709971235211564760349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1932343283003302117/1000000000000000000)
  centralHi := (193234328300330211701/100000000000000000000)
  directionLo := (199571556112734788987/100000000000000000000)
  directionHi := (49892889028183697247/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree017.table
  base := (9022507862894115352756333161325106731129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-1942556750480991874072077017364982012500000000000)
      constant := (10391340734854891899166085672117355835078346413283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree017.table
  base := (1803440513523910569917661650794649231777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-128483426718675829998096704833900000000000000)
      constant := (687360362974267435535681299753369695273074365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199571556112734788987/100000000000000000000)
  centralHi := (49892889028183697247/25000000000000000000)
  directionLo := (5142841285760546373/2500000000000000000)
  directionHi := (205713651430421854921/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree018.table
  base := (920133345939445458318879128235250365941/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-85681839967252415179905953922347654375000000000)
      constant := (465355518523031197211031771289248977759193543869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree018.table
  base := (183909346690518374643808765175945478837/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-17001352010950769400332051344370000000000000)
      constant := (92349367038660047135715151640441998936024065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5142841285760546373/2500000000000000000)
  centralHi := (205713651430421854921/100000000000000000000)
  directionLo := (211677600988899524221/100000000000000000000)
  directionHi := (105838800494449762111/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree019.table
  base := (5887405389468957650985053838261652359249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-2170171567947124054563408770907705397500000000000)
      constant := (12038847712326471881041824945521853135613785156523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree019.table
  base := (5883261545926897625701065986292009914037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-143538205456536480407216116676020000000000000)
      constant := (796388592160712914597983467012607221505809613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211677600988899524221/100000000000000000000)
  centralHi := (105838800494449762111/50000000000000000000)
  directionLo := (217478061275141980681/100000000000000000000)
  directionHi := (108739030637570990341/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree020.table
  base := (4573837635724120165460472762698486607871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-2283978976680190144809074647679067090000000000000)
      constant := (12997492878685794264592515906575547311803068539717) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree020.table
  base := (457018556117949497700177740559163128719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-75532797412733402805887911298540000000000000)
      constant := (429912210867525528647453171303109293303519155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217478061275141980681/100000000000000000000)
  centralHi := (108739030637570990341/50000000000000000000)
  directionLo := (111563891460872167747/50000000000000000000)
  directionHi := (44625556584348867099/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree021.table
  base := (3397571596333144992033680961693664784741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-799262128471085411684913508150142927500000000000)
      constant := (4680173892930947333082904551984263358189189033069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree021.table
  base := (678871815891359514836533413766462340417/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-158592984194397130816335528518140000000000000)
      constant := (928841538570724924526302997956771136677171165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111563891460872167747/50000000000000000000)
  centralHi := (44625556584348867099/20000000000000000000)
  directionLo := (228637940611683511347/100000000000000000000)
  directionHi := (57159485152920877837/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree022.table
  base := (1169863444281456202878085242741888265039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-1255796897073161162650203200610895237500000000000)
      constant := (7582332551127103828027740559198195333844783740853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree022.table
  base := (2336906269239286520362349483261843143/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-20765046695415932002611904304900000000000000)
      constant := (125402979159083443055222306319718105268025875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228637940611683511347/100000000000000000000)
  centralHi := (57159485152920877837/25000000000000000000)
  directionLo := (234018393000914288101/100000000000000000000)
  directionHi := (117009196500457144051/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree023.table
  base := (346150010537980734469163538540268448633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-656350300719847103886518069498288041875000000000)
      constant := (4091801049888429170783608692793348007900413858691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree023.table
  base := (1382127890019720084232031590263699789663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-173647762932257781225454940360260000000000000)
      constant := (1082791565236311506459578328681039098891851687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234018393000914288101/100000000000000000000)
  centralHi := (117009196500457144051/50000000000000000000)
  directionLo := (59819472497626673019/25000000000000000000)
  directionHi := (239277889990506692077/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree024.table
  base := (32443480139351575784773574445689368187/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-114133692150518937741322423115188077500000000000)
      constant := (735244649801146129500148449191773072714992212966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree024.table
  base := (516932553758443609803001324974013211449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-181175152301188106430014646281320000000000000)
      constant := (1167394851159990804423287867896027477257879601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59819472497626673019/25000000000000000000)
  centralHi := (239277889990506692077/100000000000000000000)
  directionLo := (3055302997808883331/1250000000000000000)
  directionHi := (244424239824710666481/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree025.table
  base := (-6693133697278987155563234481745570951/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-356627002543190074504675503941984444062500000000)
      constant := (2374846656048262772280726840321789819016838255615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree025.table
  base := (-53923026403638608274068012646458860947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-188702541670118431634574352202380000000000000)
      constant := (1256908491735274617897843408106803462505088985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3055302997808883331/1250000000000000000)
  centralHi := (244424239824710666481/100000000000000000000)
  directionLo := (249464445140918486233/100000000000000000000)
  directionHi := (124732222570459243117/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree026.table
  base := (-985011415269908645610760604598801019217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-2966823429078586686283069908307237245000000000000)
      constant := (20424325181235043460802068221261694184326879606741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree026.table
  base := (-986659995855800705459606686730396585193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-196229931039048756839134058123440000000000000)
      constant := (1351227787820144248419916139340783689496125343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249464445140918486233/100000000000000000000)
  centralHi := (124732222570459243117/50000000000000000000)
  directionLo := (31800601843028503369/12500000000000000000)
  directionHi := (254404814744228026953/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree027.table
  base := (-102526198340219588604888720052992389011/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-128359618242152199022030657711608289062500000000)
      constant := (913383404003038860752299688976497216310182831002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree027.table
  base := (-65674215506853348235336087205486094949/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-203757320407979082043693764044500000000000000)
      constant := (1450265116211400485940686468585239742473222475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31800601843028503369/12500000000000000000)
  centralHi := (254404814744228026953/100000000000000000000)
  directionLo := (259251056199629850711/100000000000000000000)
  directionHi := (32406382024953731339/12500000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree028.table
  base := (-2240360271255293181871040474079904192149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-3194438246544718866774401661849960630000000000000)
      constant := (23488292659328646635256246491744179024820494075177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree028.table
  base := (-1120804947536011852948401889003820458281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-105642354888454703624126734982780000000000000)
      constant := (776973552494764067573773508290875259573140831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259251056199629850711/100000000000000000000)
  centralHi := (32406382024953731339/12500000000000000000)
  directionLo := (264008353118234288207/100000000000000000000)
  directionHi := (16500522069889643013/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree029.table
  base := (-1395102956774160212828556406096403291421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-1654122827638892478510033769310661161250000000000)
      constant := (12562334041631388896665061334806229411420571644433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree029.table
  base := (-1395645953465911854745650961950466542701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-109406049572919866226406587943310000000000000)
      constant := (831106145735154654048899604621004108552616251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264008353118234288207/100000000000000000000)
  centralHi := (16500522069889643013/6250000000000000000)
  directionLo := (268681430120842072249/100000000000000000000)
  directionHi := (1074725720483368289/400000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree030.table
  base := (-329445704455544966605415248849561839649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-570342177335141841210955569232114002500000000000)
      constant := (4471591443311050443629807885452577547266025987795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree030.table
  base := (-823849948642856432044373358263989190113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-56584872128692514414343220451920000000000000)
      constant := (443752293450123350487914555907085587762396263) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268681430120842072249/100000000000000000000)
  centralHi := (1074725720483368289/400000000000000000)
  directionLo := (68318651949595541403/25000000000000000000)
  directionHi := (273274607798382165613/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree031.table
  base := (-29350673779482636997371346892780419647/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-441982559092989642188924911520505713437500000000)
      constant := (3575285149068872486562873164080025661554873756096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree031.table
  base := (-1878851900460626251562153867292549902331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-116933438941850191430966293864370000000000000)
      constant := (946147293234385003372740493353422596168212381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68318651949595541403/25000000000000000000)
  centralHi := (273274607798382165613/100000000000000000000)
  directionLo := (277791849489754194771/100000000000000000000)
  directionHi := (69447962372438548693/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree032.table
  base := (-522582026293255589623344934161808914017/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-456208485184622903469633146116925925000000000000)
      constant := (3805289760172650653763755416117057144469731087141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree032.table
  base := (-65333820541674774606298863606562997077/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-30174283406578838508311536706225000000000000)
      constant := (251754042986909308090301330111907681971723416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277791849489754194771/100000000000000000000)
  centralHi := (69447962372438548693/25000000000000000000)
  directionLo := (141118400659266349481/50000000000000000000)
  directionHi := (282236801318532698963/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree033.table
  base := (-2284209398997096786730464687961575822677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-627245881701674886333788507617794848750000000000)
      constant := (5391533362641004935514419300839291024107383147107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree033.table
  base := (-913806378489505813120862456476521641151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-248921656621561033271051999570860000000000000)
      constant := (2140192106726454831985199951798711518652311005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141118400659266349481/50000000000000000000)
  centralHi := (282236801318532698963/100000000000000000000)
  directionLo := (286612826639171112649/100000000000000000000)
  directionHi := (5732256532783422253/2000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree034.table
  base := (-2461198925843053449877265129303078346979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-1938641349471557704124198461239065392500000000000)
      constant := (17161271216125683051502861153852592318032730238767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree034.table
  base := (-153841502537512474276872843270289560121/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-32056130748811419809451463186490000000000000)
      constant := (283843554200252077018099758802418819304698684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286612826639171112649/100000000000000000000)
  centralHi := (5732256532783422253/2000000000000000000)
  directionLo := (290923035818194031429/100000000000000000000)
  directionHi := (29092303581819403143/10000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree035.table
  base := (-5244458531233339320424495145135520257561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-3991090107676181498494062799249492477500000000000)
      constant := (36362021910808571420285102007982552121063267310653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree035.table
  base := (-5244916726618570868878091596443034998819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-263976435359421683680171411412980000000000000)
      constant := (2405679987642423236680637465759873692298521269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290923035818194031429/100000000000000000000)
  centralHi := (29092303581819403143/10000000000000000000)
  directionLo := (295170312100070220649/100000000000000000000)
  directionHi := (5903406242001404413/2000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree036.table
  base := (-5536165349024753216905778736231329329327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-1368299172136415862913242892006951390000000000000)
      constant := (12822455908931318817781367319462117837973525827257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree036.table
  base := (-5536560995510914762250720876669235760591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-271503824728352008884731117334040000000000000)
      constant := (2544968872150879933857561168357573919776993641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295170312100070220649/100000000000000000000)
  centralHi := (5903406242001404413/2000000000000000000)
  directionLo := (7483933354227554587/2500000000000000000)
  directionHi := (299357334169102183481/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree037.table
  base := (-5798830774428743536903183958825736238609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-4218704925142313678985394552792215862500000000000)
      constant := (40638352635025738649126616336748510750277645748757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree037.table
  base := (-1449793041261912191889631942904870885921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-69757803524320583522322705813775000000000000)
      constant := (672150018578766220704332660371589633227090471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7483933354227554587/2500000000000000000)
  centralHi := (299357334169102183481/100000000000000000000)
  directionLo := (151743297954481474709/50000000000000000000)
  directionHi := (303486595908962949419/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree038.table
  base := (-1206711189732483819512797135041458373857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-4332512333875379769231060429563577555000000000000)
      constant := (42874785980360205079421613039156403524946132917305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree038.table
  base := (-1508462580751421345006046073787830805299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-71639650866553164823462632294040000000000000)
      constant := (709140249807505053100535378314893125110131749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151743297954481474709/50000000000000000000)
  centralHi := (303486595908962949419/100000000000000000000)
  directionLo := (307560423773912790439/100000000000000000000)
  directionHi := (7689010594347819761/2500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree039.table
  base := (-780158099788560212500514765784575139477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-185263322608685244144863596097289135312500000000)
      constant := (1882354491298638153000215292084196071676961125907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree039.table
  base := (-3120759233705090642120098181967057911491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-147042996417571492249205117548610000000000000)
      constant := (1494420539745677951865047091718634153971339541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307560423773912790439/100000000000000000000)
  centralHi := (7689010594347819761/2500000000000000000)
  directionLo := (62316198423064118471/20000000000000000000)
  directionHi := (77895248028830148089/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree040.table
  base := (-80284157791879394097171991339242022981/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-570015893917688993715299022888287617500000000000)
      constant := (5942922978688256001225058514355553325320615003130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree040.table
  base := (-6422951081577728795678010903542570725929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-301613382204073309702969941018280000000000000)
      constant := (3145431448039580291381356056168541107758838879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62316198423064118471/20000000000000000000)
  centralHi := (77895248028830148089/25000000000000000000)
  directionLo := (315550336750170695011/100000000000000000000)
  directionHi := (78887584187542673753/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree041.table
  base := (-411163128680040450448076203163328589819/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-584241820009322254996007257484707829062500000000)
      constant := (6246912680289608332496283272044129570673664238174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree041.table
  base := (-1644699520947414044707030858008877881711/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-77285192893250908726882411734835000000000000)
      constant := (826581165990072612013943862066783857132290761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315550336750170695011/100000000000000000000)
  centralHi := (78887584187542673753/25000000000000000000)
  directionLo := (31947036701191047941/10000000000000000000)
  directionHi := (319470367011910479411/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree042.table
  base := (-838680395291834911067962305370638797331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-199489248700318505425571830693709346875000000000)
      constant := (2186340253477220608753302586357347032656445557621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree042.table
  base := (-335480245173727279828368048360165268839/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-79167040235483490028022338215100000000000000)
      constant := (867878620657989634142643891801592339185311445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31947036701191047941/10000000000000000000)
  centralHi := (319470367011910479411/100000000000000000000)
  directionLo := (323342876486097081009/100000000000000000000)
  directionHi := (32334287648609708101/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree043.table
  base := (-1703922563796669868807196631040824069597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-1225387344385177555114847453355096504375000000000)
      constant := (13758474599414069996416729430552602631421015330481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree043.table
  base := (-6815829312831780682940077603109670166777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-324195550310864285316649058781460000000000000)
      constant := (3640995663020673813699582602963307386260570127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323342876486097081009/100000000000000000000)
  centralHi := (32334287648609708101/10000000000000000000)
  directionLo := (81792388150534095777/25000000000000000000)
  directionHi := (327169552602136383109/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree044.table
  base := (-6897736045405647490902317048775465128613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-5015356786273776310705055690191747710000000000000)
      constant := (57660431775346617558613544715248558281705975145849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree044.table
  base := (-3448927770081807604494278654050279930467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-165861469839897305260604382351260000000000000)
      constant := (1907381903048301888009066723192178345076083317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81792388150534095777/25000000000000000000)
  centralHi := (327169552602136383109/100000000000000000000)
  directionLo := (33095198522664996839/10000000000000000000)
  directionHi := (330951985226649968391/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree045.table
  base := (-1391180694241215251947844607331557437739/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-1709721398335614133650240522321036467500000000000)
      constant := (20117236767319909468619609612041339885750446593745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree045.table
  base := (-3478003052702902839494793751069889729023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-169625164524362467862884235311790000000000000)
      constant := (1996407609664501973654381579149175832492415673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33095198522664996839/10000000000000000000)
  centralHi := (330951985226649968391/100000000000000000000)
  directionLo := (167345837191308251621/50000000000000000000)
  directionHi := (334691674382616503243/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree046.table
  base := (-1747615908734287241068547192428087967991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-1310742900934977122799096860933617773750000000000)
      constant := (15776921759490006917591146202210522298313415553043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree046.table
  base := (-3495275873322597219658237400575800949709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-173388859208827630465164088272320000000000000)
      constant := (2087573401518759034773921875629787654926781659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167345837191308251621/50000000000000000000)
  centralHi := (334691674382616503243/100000000000000000000)
  directionLo := (338390037200592011229/100000000000000000000)
  directionHi := (33839003720059201123/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree047.table
  base := (-140032882720013964535803137902649848111/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-2678389506236487290721026660252916393750000000000)
      constant := (32964161288026309391097435918205895340940665145075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree047.table
  base := (-1750429936613430791218536350634969924839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-88576276946646396533721970616425000000000000)
      constant := (1090438988765994995624847181308487729330518289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338390037200592011229/100000000000000000000)
  centralHi := (33839003720059201123/10000000000000000000)
  directionLo := (68409682838673268739/20000000000000000000)
  directionHi := (21378025887085396481/6250000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree048.table
  base := (-6989636061534558339696202672612439109873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-1823528807068680223895906399092398160000000000000)
      constant := (22937861276931272972723573674761267350725193739943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree048.table
  base := (-1397940183342466399885584369613730711849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-361832497155515911339447588386760000000000000)
      constant := (4552640490803164802457428902440821985400203995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68409682838673268739/20000000000000000000)
  centralHi := (21378025887085396481/6250000000000000000)
  directionLo := (86417018733209950237/25000000000000000000)
  directionHi := (345668074932839800949/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree049.table
  base := (-347729992581487725291153574079109808263/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-1396098457484776690483346268512139043125000000000)
      constant := (17940860755767131950233921895662068239932777076495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree049.table
  base := (-139093109172599773421058103006979750057/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-184679943262223118272003647153910000000000000)
      constant := (2373899288055715528951616225693402221039935175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86417018733209950237/25000000000000000000)
  centralHi := (345668074932839800949/100000000000000000000)
  directionLo := (349250223197285880727/100000000000000000000)
  directionHi := (43656277899660735091/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree050.table
  base := (-431041888795124763749389611399506833137/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-712275154834021606522381368852489733125000000000)
      constant := (9347234603498077900565273576696121123669843573802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree050.table
  base := (-1379343575907347686311364369750491828939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-376887275893376561748567000228880000000000000)
      constant := (4947228671014357060748852710922633095252386945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349250223197285880727/100000000000000000000)
  centralHi := (43656277899660735091/12500000000000000000)
  directionLo := (176398000824082936851/50000000000000000000)
  directionHi := (352796001648165873703/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree051.table
  base := (-1703990071847045882710592473615437687559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8903894670042152019982118635181557500000000000)
      linear := (-484334053950436578535393068965939963125000000000)
      constant := (6488072138318888917237618932513182887734643162369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree051.table
  base := (-6816001118622646358006506817461611566489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-384414665262306886953126706149940000000000000)
      constant := (5150929482471155755926951488573792009175267439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176398000824082936851/50000000000000000000)
  centralHi := (352796001648165873703/100000000000000000000)
  directionLo := (356306496088004703433/100000000000000000000)
  directionHi := (178153248044002351717/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree052.table
  base := (-3356282520075377274802976269552288126533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-2962908028069152516335191352181320625000000000000)
      constant := (40500196535987678155718933448810133264788292058009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree052.table
  base := (-3356300004585037512101063325718650703787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-195971027315618606078843206035500000000000000)
      constant := (2679449962367788687165045338497287168092342637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356306496088004703433/100000000000000000000)
  centralHi := (178153248044002351717/50000000000000000000)
  directionLo := (89945684836075503427/25000000000000000000)
  directionHi := (359782739344302013709/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree053.table
  base := (-6586564246264899257138893638342731356933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-6039623464871371122916048581134002942500000000000)
      constant := (84208445253270718592497700637294497979147781557209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree053.table
  base := (-1646648546050700024338820319848740175973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-99867361000041884340561529498015000000000000)
      constant := (1392784771522283177086091167150279273725285123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89945684836075503427/25000000000000000000)
  centralHi := (359782739344302013709/100000000000000000000)
  directionLo := (72645142963771120201/20000000000000000000)
  directionHi := (181612857409427800503/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree054.table
  base := (-1609506223295721869338183645381714342721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8903894670042152019982118635181557500000000000)
      linear := (-512785906133703101096809538158780386250000000000)
      constant := (7290084217107424945353680197540387960896784033111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree054.table
  base := (-25148634824995079973336674649982258909/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-50874604171137232820850727989140000000000000)
      constant := (723455775115033883066601259425960299768027488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72645142963771120201/20000000000000000000)
  centralHi := (181612857409427800503/50000000000000000000)
  directionLo := (9165908993426649993/2500000000000000000)
  directionHi := (366636359737065999721/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree055.table
  base := (-3133501618955147077431876208950664646891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-3133619141168751651703690167338363163750000000000)
      constant := (45409039693755505981888021806079265092758101742743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree055.table
  base := (-6267025159037693204702930172540570183797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-414524222738028187771365529834180000000000000)
      constant := (6008420626288875646435125211433733011965708147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9165908993426649993/2500000000000000000)
  centralHi := (366636359737065999721/100000000000000000000)
  directionLo := (370015568127647736763/100000000000000000000)
  directionHi := (92503892031911934191/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree056.table
  base := (-6073546527334575693632218677910622020837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-6381045691070569393653046211448088020000000000000)
      constant := (94219643419457896543489847369738736815735020579001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree056.table
  base := (-3036782638112562837013323153501701932789/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-211025806053479256487962617877620000000000000)
      constant := (3116730911127159678996908650739239014571498739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370015568127647736763/100000000000000000000)
  centralHi := (92503892031911934191/25000000000000000000)
  directionLo := (186682096779796064633/50000000000000000000)
  directionHi := (373364193559592129267/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree057.table
  base := (-234307777697432186445128480783798920779/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-2164951033267878494632904029406483237500000000000)
      constant := (32561898610212270932119876332809453070153804884725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree057.table
  base := (-1464427618316564509519482605488350015629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-107394750368972209545121235419075000000000000)
      constant := (1615692333840430983408041271189171380671063579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186682096779796064633/50000000000000000000)
  centralHi := (373364193559592129267/100000000000000000000)
  directionLo := (188341525830061723789/50000000000000000000)
  directionHi := (376683051660123447579/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree058.table
  base := (-5619480310763344552035449484574346465161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-6608660508536701574144377964990811405000000000000)
      constant := (101216230850608315925119852385286423464730981385453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree058.table
  base := (-280974700677112777102403568513987126467/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-109276597711204790846261161899340000000000000)
      constant := (1674085696194659603114493373797906806945396585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188341525830061723789/50000000000000000000)
  centralHi := (376683051660123447579/100000000000000000000)
  directionLo := (189986461217346934359/50000000000000000000)
  directionHi := (379972922434693868719/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree059.table
  base := (-2679466062206945990793704924861699074637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-3361233958634883832195021920881086548750000000000)
      constant := (52405621816365226690884507828224419350155060966401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree059.table
  base := (-5358943833895363516041886714111891551447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-444633780213749488589604353518420000000000000)
      constant := (6934181850656155927686872476514482953627483297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (189986461217346934359/50000000000000000000)
  centralHi := (379972922434693868719/100000000000000000000)
  directionLo := (95808638101928385141/25000000000000000000)
  directionHi := (76646910481542708113/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree060.table
  base := (-1015214678950444943189034908159680072783/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-2278758442000944584878569906177844930000000000000)
      constant := (36156910035389885456578712590683467672351260848765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree060.table
  base := (-507608339813883726459262984582038452967/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-226080584791339906897082029719740000000000000)
      constant := (3588143132178539259668630405318001208759904085) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95808638101928385141/25000000000000000000)
  centralHi := (76646910481542708113/20000000000000000000)
  directionLo := (1932343283003302117/500000000000000000)
  directionHi := (386468656600660423401/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree061.table
  base := (-2385461935044580188579338533824308905747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-3475041367367949922440687797652448241250000000000)
      constant := (56097343425819831063465513444530189220404750574431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree061.table
  base := (-4770932413683531144388290484680539269999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-459688558951610138998723765360540000000000000)
      constant := (7422655800251259315879417703260202505897781449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1932343283003302117/500000000000000000)
  centralHi := (386468656600660423401/100000000000000000000)
  directionLo := (77935184072483678867/20000000000000000000)
  directionHi := (12177372511325574823/3125000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree062.table
  base := (-2221750069157536816748178479354629074709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-3531945071734482967563520736038129087500000000000)
      constant := (57991555498529801030525315442635567428679359654057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree062.table
  base := (-444350743325944139240513136986689914141/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-233607974160270232101641735640800000000000000)
      constant := (3836645134413246295198100961143136935864998455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77935184072483678867/20000000000000000000)
  centralHi := (12177372511325574823/3125000000000000000)
  directionLo := (196428500532557962967/50000000000000000000)
  directionHi := (78571400213023185187/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree063.table
  base := (-4093816132950711674521571469961081168791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-2392565850734010675124235782949206622500000000000)
      constant := (39945333376644910177414256454809432822185948190481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree063.table
  base := (-511727795022028490870693722336700370193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-59342917211183848675980397150332500000000000)
      constant := (991023688862973255810342542660780867461660343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196428500532557962967/50000000000000000000)
  centralHi := (78571400213023185187/20000000000000000000)
  directionLo := (39601252967735143231/10000000000000000000)
  directionHi := (396012529677351432311/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree064.table
  base := (-3721883558110153551214761948908824703877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-7291504960935098115618373225618981560000000000000)
      constant := (123753352223776966717487591197740670561993416808921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree064.table
  base := (-744377774520389891340607241100702915141/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-482270727058401114612402883123720000000000000)
      constant := (8187353392779793579983888127590390261622753455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39601252967735143231/10000000000000000000)
  centralHi := (396012529677351432311/100000000000000000000)
  directionLo := (199571556112734788987/50000000000000000000)
  directionHi := (15965724489018783119/4000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree065.table
  base := (-3327712245381560854297582467906347250821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-7405312369668164205864039102390343252500000000000)
      constant := (127735165576313409783970095940343212597741523660633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree065.table
  base := (-415964597481491442830907378893315898647/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-61224764553416429977120323630597500000000000)
      constant := (1056347725268458003568927075988294176276390497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199571556112734788987/50000000000000000000)
  centralHi := (15965724489018783119/4000000000000000000)
  directionLo := (40224933115247370817/10000000000000000000)
  directionHi := (402249331152473708171/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree066.table
  base := (-582262090708552202817745261534536231021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-2506373259467076765369901659720568315000000000000)
      constant := (43927146252530871871451929133063004811062677592055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree066.table
  base := (-363914290199095138209383319504326096471/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-62165688224532720627690286870730000000000000)
      constant := (1089809330583931829816025843255339970521503521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40224933115247370817/10000000000000000000)
  centralHi := (402249331152473708171/100000000000000000000)
  directionLo := (40533174658320449449/10000000000000000000)
  directionHi := (405331746583204494491/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree067.table
  base := (-2472685120276071671951121080975915518069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-7632927187134296386355370855933066637500000000000)
      constant := (135892170566401879831380059609236002718703406531337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree067.table
  base := (-2472688419115261579176880177381267126847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-504852895165192090226082000886900000000000000)
      constant := (8990431841109306772425371607422791872664728697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40533174658320449449/10000000000000000000)
  centralHi := (405331746583204494491/100000000000000000000)
  directionLo := (408390897503567972889/100000000000000000000)
  directionHi := (40839089750356797289/10000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree068.table
  base := (-201184207357595183162511878319052602573/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-3873367297933681238300518366352214165000000000000)
      constant := (70033679996831717432508051477944575830288811384645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree068.table
  base := (-502961221590200976148151993362770120853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-128095071133530603857660426701990000000000000)
      constant := (2316663331224351418583591421114629644886354003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408390897503567972889/100000000000000000000)
  centralHi := (40839089750356797289/10000000000000000000)
  directionLo := (411427302860843709841/100000000000000000000)
  directionHi := (205713651430421854921/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree069.table
  base := (-47774569040895202924121665332456510401/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-327522583525017856951945942061491250937500000000)
      constant := (6012791924653800003979643887749748113572734477964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree069.table
  base := (-152878860715205963036914547326997836251/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-259953836951526370317600706364510000000000000)
      constant := (4773569520060432788848510235119041008863811505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411427302860843709841/100000000000000000000)
  centralHi := (205713651430421854921/50000000000000000000)
  directionLo := (414441462591434096809/100000000000000000000)
  directionHi := (41444146259143409681/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree070.table
  base := (-102352164034690568045957908766142532817/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-3987174706666747328546184243123575857500000000000)
      constant := (74305554224184557671788513352430792344193056097705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree070.table
  base := (-63970230252765518275725694931250654987/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-65929382908997883229970139831260000000000000)
      constant := (1228986117476191471755844782964789222502107674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414441462591434096809/100000000000000000000)
  centralHi := (41444146259143409681/10000000000000000000)
  directionLo := (52179232322727323649/12500000000000000000)
  directionHi := (417433858581818589193/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree071.table
  base := (-124012955458295532015260407716606762641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85867500000000000000000000000000000000000000
      center := (1511268)
      previous := (755634)
      next := (755634)
      square := (5298885937339110505841371931272500000000000)
      linear := (-401118668025518783343485140002901875000000000)
      constant := (7586771779679759303602763880594038840336069573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree071.table
  base := (-496053563344162325278074338124537536249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-534962452640913391044320824571140000000000000)
      constant := (10120902984506637796800323728020522169747485199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52179232322727323649/12500000000000000000)
  centralHi := (417433858581818589193/100000000000000000000)
  directionLo := (84080991113588658549/20000000000000000000)
  directionHi := (210202477783971646373/50000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree072.table
  base := (13405085901332192711611995761692712257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8903894670042152019982118635181557500000000000)
      linear := (-683497019233302236465308353315822925000000000000)
      constant := (13117723236700134539171148053863949807227519811113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree072.table
  base := (53618859884990938803575209438897020839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-542489842009843716248880530492200000000000000)
      constant := (10414181141066604985211039754431745931991585711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84080991113588658549/20000000000000000000)
  centralHi := (210202477783971646373/50000000000000000000)
  directionLo := (423355201977799048443/100000000000000000000)
  directionHi := (105838800494449762111/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree073.table
  base := (312746208739651983945048159084988517897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-4157885819766346463914683058280618396250000000000)
      constant := (80955073025489024281279610712285809147762258833619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree073.table
  base := (312745576813526456802553379354660854233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-275008615689387020726720118206630000000000000)
      constant := (5355861690822640169812589664461286512120113617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423355201977799048443/100000000000000000000)
  centralHi := (105838800494449762111/25000000000000000000)
  directionLo := (213142515360756733573/50000000000000000000)
  directionHi := (426285030721513467147/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree074.table
  base := (1219562351201577857671136131790928843707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-8429579048265759018075031993332598485000000000000)
      constant := (166472067442492976231660314040685767612451808622489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree074.table
  base := (76222579677044536852224476801528727751/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-69693077593463045832249992791790000000000000)
      constant := (1376691210356474037286885101128226404808042398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213142515360756733573/50000000000000000000)
  centralHi := (426285030721513467147/100000000000000000000)
  directionLo := (85838971986579693347/20000000000000000000)
  directionHi := (26824678745806154171/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree075.table
  base := (1835828423729090680104228522552864687473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-2847795485666275036106899290034653392500000000000)
      constant := (57032814238986482768180677707313433752788223898457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree075.table
  base := (917913753597557138728809434647369627209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-282536005058317345931279824127690000000000000)
      constant := (5659800012518071835216187638384652734861915841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85838971986579693347/20000000000000000000)
  centralHi := (26824678745806154171/6250000000000000000)
  directionLo := (86417018733209950237/20000000000000000000)
  directionHi := (216042546833024875593/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree076.table
  base := (2474289189181190376628141151410897445803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-8657193865731891198566363746875321870000000000000)
      constant := (175789271624033022826920893924056229379232389026281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree076.table
  base := (618572102220744806998314501044691862663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-143149849871391254266779838544110000000000000)
      constant := (2907483597922702036409717376533500677135628687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86417018733209950237/20000000000000000000)
  centralHi := (216042546833024875593/50000000000000000000)
  directionLo := (217478061275141980681/50000000000000000000)
  directionHi := (434956122550283961363/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree077.table
  base := (626988686567503822913152907996095705819/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-8771001274464957288812029623646683562500000000000)
      constant := (180544553953393097141052455662913764485312971689565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree077.table
  base := (3134942768637081461080262945069365334721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-580126788854495342271679060097500000000000000)
      constant := (11944532768948078845667685941653729163717220729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217478061275141980681/50000000000000000000)
  centralHi := (434956122550283961363/100000000000000000000)
  directionLo := (437808324406419085079/100000000000000000000)
  directionHi := (10945208110160477127/2500000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree078.table
  base := (1908895067087218334906455228426286565479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-1480801447199670563176282583403007542500000000000)
      constant := (30894048254723819158124719333985220588878760286911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree078.table
  base := (763557913778257225251125153256453988801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-587654178223425667476238766018560000000000000)
      constant := (12263395145157841092615873605587325708588913245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437808324406419085079/100000000000000000000)
  centralHi := (10945208110160477127/2500000000000000000)
  directionLo := (220321032413575387573/50000000000000000000)
  directionHi := (440642064827150775147/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree079.table
  base := (28267677723835428387516909592712675843/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-1124827011491386183662920172148675868437500000000)
      constant := (23781059775054154380415392726044091007526645557220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree079.table
  base := (904565590958757528193486297732784464319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-595181567592355992680798471939620000000000000)
      constant := (12586521510532896564368795623338463246659941155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220321032413575387573/50000000000000000000)
  centralHi := (440642064827150775147/100000000000000000000)
  directionLo := (88691539544809706599/20000000000000000000)
  directionHi := (110864424431012133249/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree080.table
  base := (1050011523487438537734479959243893789559/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-9112423500664155559549027253960768640000000000000)
      constant := (195197119844945870622087801517803891453847520834465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree080.table
  base := (1312514302046061139474263536845671529037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-150677239240321579471339544465170000000000000)
      constant := (3228477964212756877924025261558946093335944613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88691539544809706599/20000000000000000000)
  centralHi := (110864424431012133249/25000000000000000000)
  directionLo := (446255565843488670989/100000000000000000000)
  directionHi := (44625556584348867099/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree081.table
  base := (2999738536936907153255055424957337539487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-1537705151566203608299115521788688388750000000000)
      constant := (33368369059516588021558540921271047386226881368183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree081.table
  base := (599947672573371270448652787941565663929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-305118173165108321544958941890870000000000000)
      constant := (6622783088602360426383086861556769926431615605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446255565843488670989/100000000000000000000)
  centralHi := (44625556584348867099/10000000000000000000)
  directionLo := (449036001253653275221/100000000000000000000)
  directionHi := (224518000626826637611/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree082.table
  base := (6771086296690055965664115866494098043431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-9340038318130287740040359007503492025000000000000)
      constant := (205287761648862394568077280415623596629819029491837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree082.table
  base := (6771086000581255918084070609836330451129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-617763735699146968294477589702800000000000000)
      constant := (13581484465790925729452813400995896147334975921) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449036001253653275221/100000000000000000000)
  centralHi := (224518000626826637611/50000000000000000000)
  directionLo := (225899662902277013841/50000000000000000000)
  directionHi := (451799325804554027683/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree083.table
  base := (7564884858724799627480832763333829803109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-9453845726863353830286024884274853717500000000000)
      constant := (210429761646274415512125514244900944326160316892743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree083.table
  base := (3782442303453874856616459601714335274179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-312645562534038646749518647811930000000000000)
      constant := (6960833358867219492761012799373882424554075371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225899662902277013841/50000000000000000000)
  centralHi := (451799325804554027683/100000000000000000000)
  directionLo := (454545851562884920881/100000000000000000000)
  directionHi := (227272925781442460441/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree084.table
  base := (8380872401096822465707344659001506349217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-3189217711865473306843896920348738470000000000000)
      constant := (71878738095732579310550818889481450506554806767753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree084.table
  base := (8380872186976948796382514191414433828207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-632818514437007618703597001544920000000000000)
      constant := (14266112928939538348607949961011103852899141943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454545851562884920881/100000000000000000000)
  centralHi := (227272925781442460441/50000000000000000000)
  directionLo := (91455176244673404539/20000000000000000000)
  directionHi := (57159485152920877837/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree085.table
  base := (1152381077786213865771447149238810307789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-1210182568041185751347169579727197137812500000000)
      constant := (27613389939928354623802776927293878508866606945103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree085.table
  base := (921904844024910238974833712902558067809/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-320172951902968971954078353732990000000000000)
      constant := (7307411547982672106027865768055881936591726205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91455176244673404539/20000000000000000000)
  centralHi := (57159485152920877837/12500000000000000000)
  directionLo := (91997941699624023357/20000000000000000000)
  directionHi := (229994854249060058393/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree086.table
  base := (10079413268981918374953664146556443783993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-9795267953062552101023022514588938795000000000000)
      constant := (226242477299100802635606917197621420197529638965411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree086.table
  base := (10079413114235570437091463793592445677911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-647873293174868269112716413387040000000000000)
      constant := (14967797215921114135861490880624399910566403039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91997941699624023357/20000000000000000000)
  centralHi := (229994854249060058393/50000000000000000000)
  directionLo := (2891797615534243771/625000000000000000)
  directionHi := (462687618485479003361/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree087.table
  base := (219239322566857664262236857020521812721/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-1651512560299269698544781398560050081250000000000)
      constant := (38607047931561577437957250905535196048491904922225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree087.table
  base := (1096196599681594881173679648429095839311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-327700341271899297158638059654050000000000000)
      constant := (7662517643189140806589462400486138591321358195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2891797615534243771/625000000000000000)
  centralHi := (462687618485479003361/100000000000000000000)
  directionLo := (465369888019565383547/100000000000000000000)
  directionHi := (116342472004891345887/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree088.table
  base := (2966676755390192222170718598056669644593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-2505720692632171070378588567032915545000000000000)
      constant := (59276637589818191140107127938497289893637775121611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree088.table
  base := (11866706909783772999051966017808747629543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-662928071912728919521835825229160000000000000)
      constant := (15686537305296560831780007302375652351610637807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465369888019565383547/100000000000000000000)
  centralHi := (116342472004891345887/25000000000000000000)
  directionLo := (468036786001828576203/100000000000000000000)
  directionHi := (117009196500457144051/25000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree089.table
  base := (3198408949601221788347332246766968346509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-2534172544815437592940005036225755968125000000000)
      constant := (60658816395699819068981051194011299887029234944543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree089.table
  base := (3198408925856074484927755223416638028641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-167613865320414811181598882787555000000000000)
      constant := (4013075817740466918870128891526384588789910809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468036786001828576203/100000000000000000000)
  centralHi := (117009196500457144051/25000000000000000000)
  directionLo := (117672143428919735933/25000000000000000000)
  directionHi := (470688573715678943733/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree090.table
  base := (3435688083164341298555829493765886094571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8903894670042152019982118635181557500000000000)
      linear := (-854208132332901371833807168472865463750000000000)
      constant := (20685702769841269164192569256687168346403233373539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree090.table
  base := (13742752251959289247216457641039030614447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-677982850650589569930955237071280000000000000)
      constant := (16422333181934167138789439674924455861504803703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117672143428919735933/25000000000000000000)
  centralHi := (470688573715678943733/100000000000000000000)
  directionLo := (473325505125256042517/100000000000000000000)
  directionHi := (236662752562628021259/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree091.table
  base := (14714056518275076611077714090529774389347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-10364304996727882552251351898445747257500000000000)
      constant := (253886053306799976537504949506111421620634744002769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree091.table
  base := (3678514112430041799188127863615330107483/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-171377560004879973783878735748085000000000000)
      constant := (4199156759250914913109340984393659414400572867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473325505125256042517/100000000000000000000)
  centralHi := (236662752562628021259/50000000000000000000)
  directionLo := (475947827159298456367/100000000000000000000)
  directionHi := (29746739197456153523/6250000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree092.table
  base := (15707548266165082394090141994198464351713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-10478112405460948642497017775217108950000000000000)
      constant := (259608125773487677014424803561515305448800051797851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree092.table
  base := (15707548207933025334100242510745323753347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-693037629388450220340074648913400000000000000)
      constant := (17175184835153972761429935712020403211652069803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475947827159298456367/100000000000000000000)
  centralHi := (29746739197456153523/6250000000000000000)
  directionLo := (478555779981013384153/100000000000000000000)
  directionHi := (239277889990506692077/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree093.table
  base := (16723227501475498631814101899668684087843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-3530639938064671577580894550662823547500000000000)
      constant := (88464883541732744891204388011861801291531312829787) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree093.table
  base := (2090403431502209601237705762312699538639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-87570627344672568193079294354307500000000000)
      constant := (2194750821941404738316106900290131847017877911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478555779981013384153/100000000000000000000)
  centralHi := (239277889990506692077/50000000000000000000)
  directionLo := (240574798622390383393/50000000000000000000)
  directionHi := (481149597244780766787/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree094.table
  base := (17761094161319391694686137695805933323039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-10705727222927080822988349528759832335000000000000)
      constant := (271245627851043202890312591535967018889422805906853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree094.table
  base := (1776109411931853176570566792603645259719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-354046204063155435374597030377760000000000000)
      constant := (8972546128709055619722358143945495672892614155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240574798622390383393/50000000000000000000)
  centralHi := (481149597244780766787/100000000000000000000)
  directionLo := (241864753170234271737/50000000000000000000)
  directionHi := (19349180253618741739/4000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree095.table
  base := (18821148192862477008272119392928506014501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-10819534631660146913234015405531194027500000000000)
      constant := (277161057441874683137069239097309183206170861934727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree095.table
  base := (18821148157198255441500550397769699516889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-715619797495241195953753766676580000000000000)
      constant := (18336441880211947914510144356018415289768862161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241864753170234271737/50000000000000000000)
  centralHi := (19349180253618741739/4000000000000000000)
  directionLo := (486295728626082063349/100000000000000000000)
  directionHi := (9725914572521641267/2000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree096.table
  base := (621980923491139551868408837130479797879/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-455555918349717208478320053429273155000000000000)
      constant := (11797539141250297659604814281120960509684103754044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree096.table
  base := (199033895214361998817639470644547761921/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-180786796716042880289578368149410000000000000)
      constant := (4683013860851616433320591015551475683155838225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486295728626082063349/100000000000000000000)
  centralHi := (9725914572521641267/2000000000000000000)
  directionLo := (488848479649421332961/100000000000000000000)
  directionHi := (244424239824710666481/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree097.table
  base := (10503909100294600556466546635473473542651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-5523574724563139546862673579536958706250000000000)
      constant := (144592636844491850323083348296736217574339341274777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree097.table
  base := (10503909087441439380492204383783068316967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-365337288116550923181436589259350000000000000)
      constant := (9565966473288170113410297412518747349160955183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488848479649421332961/100000000000000000000)
  centralHi := (244424239824710666481/50000000000000000000)
  directionLo := (245693984679687140013/50000000000000000000)
  directionHi := (491387969359374280027/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree098.table
  base := (22134434108150539418394262953225905950577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-11160956857859345183971013035845279105000000000000)
      constant := (295294060333379751358264662225077788024406404291979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree098.table
  base := (11067217043164773807570655820814941011941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-369100982801016085783716442219880000000000000)
      constant := (9768037194682131239878132260938690259645712509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245693984679687140013/50000000000000000000)
  centralHi := (491387969359374280027/100000000000000000000)
  directionLo := (493914402307432223183/100000000000000000000)
  directionHi := (30869650144214513949/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree099.table
  base := (11641618624039744178463279452629239198979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-1879127377765401879036113152102773466250000000000)
      constant := (50244549886439665739354548332218880328285581388411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree099.table
  base := (2910404653694812260406960010685220391243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-93216169371370312096499073795102500000000000)
      constant := (2493059971433758243633065607633478838259341107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493914402307432223183/100000000000000000000)
  centralHi := (30869650144214513949/6250000000000000000)
  directionLo := (99285595567994990517/20000000000000000000)
  directionHi := (248213988919987476293/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree100.table
  base := (4890845519652726746121196188353608186189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-11388571675325477364462344789388002490000000000000)
      constant := (307704990640929815128765401805351524504751901459515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree100.table
  base := (24454227582545174057623699586988667884967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-753256744339892821976552296281880000000000000)
      constant := (20357149092641591491868274870259433258614987183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99285595567994990517/20000000000000000000)
  centralHi := (248213988919987476293/50000000000000000000)
  directionLo := (498928890281836972467/100000000000000000000)
  directionHi := (124732222570459243117/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree101.table
  base := (6411851285031628087147907235916429763381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-2875594771014635863677002666539841045625000000000)
      constant := (78501783574259706163267521842747195899870945270487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree101.table
  base := (5129481025357567483729757932339521799161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-760784133708823147181112002202940000000000000)
      constant := (20774082352667012708436253299485685925392971445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498928890281836972467/100000000000000000000)
  centralHi := (124732222570459243117/25000000000000000000)
  directionLo := (250708664555816642853/50000000000000000000)
  directionHi := (501417329111633285707/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree102.table
  base := (13431384929031241053776047181191127979191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-1936031082131934924158946090488454312500000000000)
      constant := (53395621714043835295977246527278398649549872863119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree102.table
  base := (67156924616860979971718936476822940511/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-96038940384719184048208963515500000000000000)
      constant := (2649409943921048517453827642517642292295521950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250708664555816642853/50000000000000000000)
  centralHi := (501417329111633285707/100000000000000000000)
  directionLo := (503893479129292386661/100000000000000000000)
  directionHi := (251946739564646193331/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree103.table
  base := (14050160869480954181000911811281429697537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-5864996950762337817599671209851043783750000000000)
      constant := (163402389300166266024917603727739016499020815131899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree103.table
  base := (28100321729359234662140895212600395117821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-775838912446683797590231414045060000000000000)
      constant := (21620740688596244185495373618985971923703932629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503893479129292386661/100000000000000000000)
  centralHi := (251946739564646193331/50000000000000000000)
  directionLo := (506357520616215667973/100000000000000000000)
  directionHi := (253178760308107833987/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree104.table
  base := (14680030385906115995366497812040489120839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-5921900655128870862722504148236724630000000000000)
      constant := (166650139621670317725605532981748552866040457407453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree104.table
  base := (7340015190916435407148339270596100015923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-195841575453903530698697779991530000000000000)
      constant := (5512616441056255992506266221255054749082302427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (506357520616215667973/100000000000000000000)
  centralHi := (253178760308107833987/50000000000000000000)
  directionLo := (31800601843028503369/6250000000000000000)
  directionHi := (101761925897691210781/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree105.table
  base := (30641986947362791755157657707533065273911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-3985869572996935938563558057748270317500000000000)
      constant := (113286744070561877547086039880318416012585946483599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree105.table
  base := (15320993470226149295533939616102242025513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-395446845592272223999675412943590000000000000)
      constant := (11242227389074631860566802169121329568950098337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31800601843028503369/6250000000000000000)
  centralHi := (101761925897691210781/20000000000000000000)
  directionLo := (511249977443284178709/100000000000000000000)
  directionHi := (51124997744328417871/10000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree106.table
  base := (31946100257843211910934343573526454278799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-12071416127723873905936340050016172645000000000000)
      constant := (346484637504022135688598560022863865546824216544373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree106.table
  base := (31946100251981716940170316702491796392133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-798421080553474773203910531808240000000000000)
      constant := (22922707730280380366432038413011188576893530717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511249977443284178709/100000000000000000000)
  centralHi := (51124997744328417871/10000000000000000000)
  directionLo := (513678732099487680057/100000000000000000000)
  directionHi := (256839366049743840029/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree107.table
  base := (33272400696726794545951015214678738530717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (2661648)
      previous := (1330824)
      next := (1330824)
      square := (9332407724736293496356487345810000000000000)
      linear := (-1064304614940775613257228223145037500000000000)
      constant := (30847540843673691244220032008304491094050033191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree107.table
  base := (16636200345877750909410512868365215005879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (88)
      previous := (44)
      next := (44)
      square := (308550146291618511418253235000000000000)
      linear := (-35197330331138313320310517850000000000000)
      constant := (1020404603919293066569205269803365215005879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513678732099487680057/100000000000000000000)
  centralHi := (256839366049743840029/50000000000000000000)
  directionLo := (129024014282932008729/25000000000000000000)
  directionHi := (516096057131728034917/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree108.table
  base := (6924177651706344862991287280592532229447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-4099676981730002028809223934519632010000000000000)
      constant := (119975601685443453180664320265112686634679930009115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree108.table
  base := (34620888254315802330485549101733483585649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-813475859291335423613029943650360000000000000)
      constant := (23812005448877553601828052902218706653572095401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129024014282932008729/25000000000000000000)
  centralHi := (516096057131728034917/100000000000000000000)
  directionLo := (259251056199629850711/50000000000000000000)
  directionHi := (518502112399259701423/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree109.table
  base := (7198312587730808548228379377427873881797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-12412838353923072176673337680330257722500000000000)
      constant := (366744567314555796921703338265036213943997995694595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree109.table
  base := (17995781467539510164453382032331645301299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-410501624330132874408794824785710000000000000)
      constant := (12131525107614322820917356258813340007054572251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259251056199629850711/50000000000000000000)
  centralHi := (518502112399259701423/100000000000000000000)
  directionLo := (260448527034649014429/50000000000000000000)
  directionHi := (520897054069298028859/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree110.table
  base := (9346106183306828755042697638137705804769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-3131661440664034566729750889275404853750000000000)
      constant := (93406695473306739048799581323813188897945586649563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree110.table
  base := (37384424730196017160459312922927320744139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-828530638029196074022149355492480000000000000)
      constant := (24718358919553179969876284393844394895199647411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260448527034649014429/50000000000000000000)
  centralHi := (520897054069298028859/100000000000000000000)
  directionLo := (523281034735305352937/100000000000000000000)
  directionHi := (261640517367652676469/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree111.table
  base := (38799473639004723664514244600002062602831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-4213484390463068119054889811290993702500000000000)
      constant := (126857816263927224301735713531287515491747142891879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree111.table
  base := (38799473636434666713694158222798949543749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-836058027398126399226709061413540000000000000)
      constant := (25177931561814151974102788501064135173326382301) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523281034735305352937/100000000000000000000)
  centralHi := (261640517367652676469/50000000000000000000)
  directionLo := (65706775441306101047/12500000000000000000)
  directionHi := (525654203530448808377/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree112.table
  base := (40236709653260005041169280172664208717919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-12754260580122270447410335310644342800000000000000)
      constant := (387584568009747912968658904700981463524822028384613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree112.table
  base := (40236709651081182780372016224378138817823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-843585416767056724431268767334600000000000000)
      constant := (25641768141980491516216093279747785311325255527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65706775441306101047/12500000000000000000)
  centralHi := (525654203530448808377/100000000000000000000)
  directionLo := (264008353118234288207/50000000000000000000)
  directionHi := (105603341247293715283/20000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree113.table
  base := (41696132773704217614390789872954022560057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-12868067988855336537656001187415704492500000000000)
      constant := (394660139546729361661640373872330372738210320283939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree113.table
  base := (20848066385928609863792201315729872008399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-425556403067993524817914236627830000000000000)
      constant := (13054934330013056908532514746594046304624160151) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264008353118234288207/50000000000000000000)
  centralHi := (105603341247293715283/20000000000000000000)
  directionLo := (265184342694090730321/50000000000000000000)
  directionHi := (530368685388181460643/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree114.table
  base := (21588871499207905961570461666583553309479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-2163645899598067104650277844031177697500000000000)
      constant := (66966693900398885951604557321016966358064074582911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree114.table
  base := (43177742996850225193755295154159407513351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-858640195504917374840388179176720000000000000)
      constant := (26582233115929122064661913262188171056620355599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265184342694090730321/50000000000000000000)
  centralHi := (530368685388181460643/100000000000000000000)
  directionLo := (5327102803738317757/1000000000000000000)
  directionHi := (532710280373831775701/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree115.table
  base := (44681540325781876632421544007043534430903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-13095682806321468718147332940958427877500000000000)
      constant := (409004639576460510439213359461689661306633403943981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree115.table
  base := (44681540324454926546721239778287472055561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-866167584873847700044947885097780000000000000)
      constant := (27058861509671137492641105201739563267564117889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5327102803738317757/1000000000000000000)
  centralHi := (532710280373831775701/100000000000000000000)
  directionLo := (66880203441436184019/12500000000000000000)
  directionHi := (535041627531489472153/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree116.table
  base := (46207524754448774691285207085987487438089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-13209490215054534808392998817729789570000000000000)
      constant := (416273568068696572763210616477529284849152692173203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree116.table
  base := (9241504950664834288066211213072001769567/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-873694974242778025249507591018840000000000000)
      constant := (27539753841236736553791520447002066741298862915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66880203441436184019/12500000000000000000)
  centralHi := (535041627531489472153/100000000000000000000)
  directionLo := (537362860241684144499/100000000000000000000)
  directionHi := (1074725720483368289/200000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree117.table
  base := (9551139256656133807161248134980742564681/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-4441099207929200299546221564833717087500000000000)
      constant := (141202316292968280062341606284520223743602290942645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree117.table
  base := (47755696282327627277263850320682211569107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-881222363611708350454067296939900000000000000)
      constant := (28024910110612978070206432086065120640254706043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537362860241684144499/100000000000000000000)
  centralHi := (1074725720483368289/200000000000000000)
  directionLo := (269837054508226510281/50000000000000000000)
  directionHi := (539674109016453020563/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree118.table
  base := (24663027455662338534712219874723007879929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-6718552516260333494442165285636256477500000000000)
      constant := (215502391003460163771467696796043453357039835590883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree118.table
  base := (6165756863814635422910906948800338747033/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-111093719122579834457328375357620000000000000)
      constant := (3564291289723625747234569218709260078314780817) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269837054508226510281/50000000000000000000)
  centralHi := (539674109016453020563/100000000000000000000)
  directionLo := (54197550158497115651/10000000000000000000)
  directionHi := (541975501584971156511/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree119.table
  base := (25459300318890797312840470814114263869707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-6775456220626866539564998224021937323750000000000)
      constant := (219233533726302329021264904022851484596646202524489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree119.table
  base := (254593003185486502458343209251823332163/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-112034642793696125107898338597752500000000000)
      constant := (3626001807844464447804632944585296883248354675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54197550158497115651/10000000000000000000)
  centralHi := (541975501584971156511/100000000000000000000)
  directionLo := (544267162975922814159/100000000000000000000)
  directionHi := (6803339537199035177/1250000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree120.table
  base := (52533333461981299394058252324342192346969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-4554906616662266389791887441605078780000000000000)
      constant := (148664601738613934848826789088520776295069638776321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree120.table
  base := (52533333461401520833309804034322242456297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-903804531718499326067746414703080000000000000)
      constant := (29505962545505473174189556157286555353882144353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544267162975922814159/100000000000000000000)
  centralHi := (6803339537199035177/1250000000000000000)
  directionLo := (68318651949595541403/12500000000000000000)
  directionHi := (21861968623870573249/4000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree121.table
  base := (54170253383362086014079775965592484957667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-13778527258719865259621328201586598032500000000000)
      constant := (453584995296534511576050955184378346224550672771409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree121.table
  base := (54170253382870893859356460830341445142771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-911331921087429651272306120624140000000000000)
      constant := (30008174566031880473200198884746289205439585179) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68318651949595541403/12500000000000000000)
  centralHi := (21861968623870573249/4000000000000000000)
  directionLo := (274410889655010334857/50000000000000000000)
  directionHi := (109764355862004133943/20000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree122.table
  base := (13957340100363326134808488300138862032229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-3473083666863232837466748519589489931250000000000)
      constant := (115310159423650322320178795755810862543649157062983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree122.table
  base := (27914680200518595849592152145917183920441/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-459429655228179988238432913272600000000000000)
      constant := (15257325262164788369289107018690545838705129009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274410889655010334857/50000000000000000000)
  centralHi := (109764355862004133943/20000000000000000000)
  directionLo := (551084971506750204911/100000000000000000000)
  directionHi := (34442810719171887807/6250000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree123.table
  base := (57510654515860774372901232940556282984883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-4668714025395332480037553318376440472500000000000)
      constant := (156320244136657962653317852138457707634803028279147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree123.table
  base := (14377663628877072124820880594600726290071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-231596674956322575420356383116565000000000000)
      constant := (7756347605098518130356691944285111215295022879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551084971506750204911/100000000000000000000)
  centralHi := (34442810719171887807/6250000000000000000)
  directionLo := (553338907177305162221/100000000000000000000)
  directionHi := (276669453588652581111/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree124.table
  base := (59214135726254530134989197243836734148071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-14119949484919063530358325831900683110000000000000)
      constant := (476745279442595176343058592560098642024038108765117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree124.table
  base := (59214135725955961840194938300025848776077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-933914089194220626885985238387320000000000000)
      constant := (31540394254221610003265471988955395942637305573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553338907177305162221/100000000000000000000)
  centralHi := (276669453588652581111/50000000000000000000)
  directionLo := (277791849489754194771/50000000000000000000)
  directionHi := (555583698979508389543/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree125.table
  base := (60939804032358526794400041750491048766787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-14233756893652129620603991708672044802500000000000)
      constant := (484594278792417359102548702257931256068877121601649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree125.table
  base := (60939804032105645045442269101708752739917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-941441478563150952090544944308380000000000000)
      constant := (32059662025809045670215349709274213510119309733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277791849489754194771/50000000000000000000)
  centralHi := (555583698979508389543/100000000000000000000)
  directionLo := (34863716081522552421/6250000000000000000)
  directionHi := (557819457304360838737/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree126.table
  base := (31343829716970995476484598339376543798271/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-2391260717064199285141609597573901082500000000000)
      constant := (82084621743233413231259986003298214988467325986839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree126.table
  base := (31343829716863909262938994396937050128219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-474484433966040638647552325114720000000000000)
      constant := (16291596867576875876250125456521112286917979331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34863716081522552421/6250000000000000000)
  centralHi := (557819457304360838737/100000000000000000000)
  directionLo := (5600462903393881939/1000000000000000000)
  directionHi := (560046290339388193901/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree127.table
  base := (64457701930812155201050420966563620517923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-14461371711118261801095323462214768187500000000000)
      constant := (500485634443511160826725652739767901241807849557521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree127.table
  base := (12891540386126155629847710650476355253063/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-956496257301011602499664356150500000000000000)
      constant := (33110989382253533429509890283582148956461591435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5600462903393881939/1000000000000000000)
  centralHi := (560046290339388193901/100000000000000000000)
  directionLo := (140566076032432375207/25000000000000000000)
  directionHi := (562264304129729500829/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree128.table
  base := (13249986304561630900831226069407710659251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-14575179119851327891340989338986129880000000000000)
      constant := (508527990744721550728863265786464348691125077714885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree128.table
  base := (66249931522654560503797917426092759554571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-964023646669941927704224062071560000000000000)
      constant := (33643048967106559280143416331103496004140283379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140566076032432375207/25000000000000000000)
  centralHi := (562264304129729500829/100000000000000000000)
  directionLo := (141118400659266349481/25000000000000000000)
  directionHi := (22578944105482615917/4000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree129.table
  base := (3403217410489794945082294522538245897431/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8903894670042152019982118635181557500000000000)
      linear := (-1224082210715366165132221267979790964375000000000)
      constant := (43052899946917369360456597280539730075545461416395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree129.table
  base := (68064348209665840110320211764924984256363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-971551036038872252908783767992620000000000000)
      constant := (34179372489711302860989057585127376144751099987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141118400659266349481/25000000000000000000)
  centralHi := (22578944105482615917/4000000000000000000)
  directionLo := (70834285974559825237/12500000000000000000)
  directionHi := (566674287796478601897/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree130.table
  base := (4368809499478985404741519926915972735377/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-1850349242164682508979040136566106658125000000000)
      constant := (65600757537294059879693322036124663983010006683158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree130.table
  base := (13980190398310728639595493143355132787283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-979078425407802578113343473913680000000000000)
      constant := (34719959950066493633344604610802764576408015335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70834285974559825237/12500000000000000000)
  centralHi := (566674287796478601897/100000000000000000000)
  directionLo := (568866459571334641779/100000000000000000000)
  directionHi := (28443322978566732089/5000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree131.table
  base := (14351948573663797097057458652265934500917/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-14916601346050526162077986969300214957500000000000)
      constant := (533041773550737628066363596133581145389078269195795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree131.table
  base := (71759742868225747496424126224354044357241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-986605814776732903317903179834740000000000000)
      constant := (35264811348171075744436871171176739453846052209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (568866459571334641779/100000000000000000000)
  centralHi := (28443322978566732089/5000000000000000000)
  directionLo := (285525108003133221663/50000000000000000000)
  directionHi := (571050216006266443327/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree132.table
  base := (36820360419842297752967897094099070978363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-2505068125797265375387275474345262775000000000000)
      constant := (90223656520025092372628535212375100277715272332467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree132.table
  base := (18410180209901414590757024517371441829439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-248533301036415807130615721438950000000000000)
      constant := (8953481671006043351775590602024105637505247111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285525108003133221663/50000000000000000000)
  centralHi := (571050216006266443327/100000000000000000000)
  directionLo := (573225653278342225299/100000000000000000000)
  directionHi := (5732256532783422253/1000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree133.table
  base := (18885971476424223757063993878329669383003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-3786054040879164585642329680710734585625000000000)
      constant := (137426639251645057015210124366836648437636550870681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree133.table
  base := (15108777181126013819170410605286307679861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1001660593514593553727022591676860000000000000)
      constant := (36367305957625061822910597850705324683133642945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573225653278342225299/100000000000000000000)
  centralHi := (5732256532783422253/1000000000000000000)
  directionLo := (71924108218311532937/12500000000000000000)
  directionHi := (575392865746492263497/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree134.table
  base := (19367309516575824436698420193588130232131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-3814505893062431108203746149903575008750000000000)
      constant := (139533906802504386144737278590604221265568670426737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree134.table
  base := (77469238066246728012442443947512769555673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1009187982883523878931582297597920000000000000)
      constant := (36924949168973142762349166837709673698642900177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71924108218311532937/12500000000000000000)
  centralHi := (575392865746492263497/100000000000000000000)
  directionLo := (577551945999266392483/100000000000000000000)
  directionHi := (144387986499816598121/25000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree135.table
  base := (1985419433036513305169458503302126250667/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-640492957540949605127527103182735905312500000000)
      constant := (23609547905435625484615879206369624365921127554015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree135.table
  base := (79416777321412647249692453728943293298837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1016715372252454204136142003518980000000000000)
      constant := (37486856318067924057373359420088221764978384813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577551945999266392483/100000000000000000000)
  centralHi := (144387986499816598121/25000000000000000000)
  directionLo := (5797029849009906351/1000000000000000000)
  directionHi := (579702984900990635101/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree136.table
  base := (81386503671133129912818053234576695366603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-15485638389715856613306316353157023420000000000000)
      constant := (575187124567886488086587468982111640144769591447881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree136.table
  base := (16277300734218519727457329383715658656191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1024242761621384529340701709440040000000000000)
      constant := (38053027404909002380661234177349362879773653795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5797029849009906351/1000000000000000000)
  centralHi := (579702984900990635101/100000000000000000000)
  directionLo := (581846071636388062859/100000000000000000000)
  directionHi := (29092303581819403143/5000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree137.table
  base := (83378417115292155777591852905039264853099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-15599445798448922703551982229928385112500000000000)
      constant := (583809551722306964031975939408388664075404491810473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree137.table
  base := (83378417115257850732652256311921841816433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1031770150990314854545261415361100000000000000)
      constant := (38623462429496048785926775497768823166956341417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (581846071636388062859/100000000000000000000)
  centralHi := (29092303581819403143/5000000000000000000)
  directionLo := (291990646876862942169/50000000000000000000)
  directionHi := (583981293753725884339/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree138.table
  base := (10674064706739267769912674638973899116729/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-654718883632582866408235337779156116875000000000)
      constant := (24687351299738015675154811133711957253244511248161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree138.table
  base := (85392517653885108444546743391495879910733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1039297540359245179749821121282160000000000000)
      constant := (39198161391828796567670347557859996329097982117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291990646876862942169/50000000000000000000)
  centralHi := (583981293753725884339/100000000000000000000)
  directionLo := (586108737206547822447/100000000000000000000)
  directionHi := (36631796075409238903/6250000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree139.table
  base := (4371440264349009696485364093109707372981/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-3956765153978763721010828495867777124375000000000)
      constant := (150311940745524863259582025787091121269988427248435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree139.table
  base := (4371440264347781141928072874606362954203/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-261706232432043876238595206800805000000000000)
      constant := (9944281072976757767335476429039328747313350735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586108737206547822447/100000000000000000000)
  centralHi := (36631796075409238903/6250000000000000000)
  directionLo := (588228486394048064457/100000000000000000000)
  directionHi := (294114243197024032229/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree140.table
  base := (3579491200579009488721071948747911087023/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-15940868024648120974288979860242470190000000000000)
      constant := (610063547087465584597183148071543601290406001080525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree140.table
  base := (89487280014454443898406711126574418375059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1054352319097105830158940533124280000000000000)
      constant := (40360351129730581128204949340619350515976050491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588228486394048064457/100000000000000000000)
  centralHi := (294114243197024032229/50000000000000000000)
  directionLo := (295170312100070220649/50000000000000000000)
  directionHi := (590340624200140441299/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree141.table
  base := (45783970918193694423969609058188480461511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-2675779238896864510755774289502305313750000000000)
      constant := (103157297251634785564797570145793146869741029611999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree141.table
  base := (18313588367273958673877450939223549743271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1061879708466036155363500239045340000000000000)
      constant := (40947841905299311895021472518590362105053548395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295170312100070220649/50000000000000000000)
  centralHi := (590340624200140441299/100000000000000000000)
  directionLo := (296222616015637002883/50000000000000000000)
  directionHi := (592445232031274005767/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree142.table
  base := (23417697688176856789573254658072023241421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 85867500000000000000000000000000000000000000
      center := (1511268)
      previous := (755634)
      next := (755634)
      square := (5298885937339110505841371931272500000000000)
      linear := (-801848980465892340546534001873893750000000000)
      constant := (31139083130783933879436860077508541813523087087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree142.table
  base := (46835395376346269233662362155373766917199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-534703548917483240284029972483200000000000000)
      constant := (20769798309306559404272708580946814257435011351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296222616015637002883/50000000000000000000)
  centralHi := (592445232031274005767/100000000000000000000)
  directionLo := (594542389853043824461/100000000000000000000)
  directionHi := (297271194926521912231/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree143.table
  base := (47897913381714173992234242295881997827367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-8141145125423659622512988745278277633750000000000)
      constant := (318448806652709979971028364228089655864802936293309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree143.table
  base := (478979133817078751542639968760986001647/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-134616810900487100721577456360932500000000000)
      constant := (5266951908708990317498425445807026968321412575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594542389853043824461/100000000000000000000)
  centralHi := (297271194926521912231/50000000000000000000)
  directionLo := (298316088112821783797/50000000000000000000)
  directionHi := (119326435245128713519/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree144.table
  base := (24485762467136248042628216733226588083981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8903894670042152019982118635181557500000000000)
      linear := (-1366341471631698777939303613943993080000000000000)
      constant := (53830933889890497642262567600212650644353405782229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree144.table
  base := (9794304986853433349767438778802250785131/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-542230938286413565488589678404260000000000000)
      constant := (21367948929237832376083191211770934846194824095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298316088112821783797/50000000000000000000)
  centralHi := (119326435245128713519/20000000000000000000)
  directionLo := (598714668338204366961/100000000000000000000)
  directionHi := (299357334169102183481/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree145.table
  base := (25028115017013433290235192379941544832593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 432858067500000000000000000000000000000000000000
      center := (7618301988)
      previous := (3809150994)
      next := (3809150994)
      square := (26711684010126456059946355905544672500000000000)
      linear := (-4127476267078362856379327311024819663125000000000)
      constant := (163777313092231162531681864700912046848563139297611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree145.table
  base := (100112460068044715479133921550902531201659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1091989265941757456181739062729580000000000000)
      constant := (43340444385024304542892946036404633079727793891) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (598714668338204366961/100000000000000000000)
  centralHi := (299357334169102183481/50000000000000000000)
  directionLo := (300394971021031204211/50000000000000000000)
  directionHi := (600789942042062408423/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree146.table
  base := (102304057361952215051694148549811516606459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-16623712477046517515762975120870640345000000000000)
      constant := (664311750376135587291955559160190716385131400303193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree146.table
  base := (102304057361944586079289762386433881740883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1099516655310687781386298768650640000000000000)
      constant := (43949254849317815462989355287984241512051369467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300394971021031204211/50000000000000000000)
  centralHi := (600789942042062408423/100000000000000000000)
  directionLo := (75357258985374478093/12500000000000000000)
  directionHi := (120571614376599164949/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree147.table
  base := (52258920875119566508909315877574646772239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-2789586647629930601001440166273667006250000000000)
      constant := (112263116783386426213538640354992846661140406491751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree147.table
  base := (104517841750232679198185799524188068252457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1107044044679618106590858474571700000000000000)
      constant := (44562329251356183016877212666070059193422380193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75357258985374478093/12500000000000000000)
  centralHi := (120571614376599164949/20000000000000000000)
  directionLo := (30245956556623482583/5000000000000000000)
  directionHi := (604919131132469651661/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree148.table
  base := (13344226654114256165960061704249146117747/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-2106415911814081212031788359301670466250000000000)
      constant := (85363762917684185538036085562191974594883737549569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree148.table
  base := (106753813232908589894916160739503349412063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1114571434048548431795418180492760000000000000)
      constant := (45179667591139402568388086839561933847418709287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30245956556623482583/5000000000000000000)
  centralHi := (604919131132469651661/100000000000000000000)
  directionLo := (606973191817925898837/100000000000000000000)
  directionHi := (303486595908962949419/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree149.table
  base := (109011971809977239239297117427209641196729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-16965134703245715786499972751184725422500000000000)
      constant := (692305958299600416020187473619346210570595050904483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree149.table
  base := (1703312059530822206119866256780404732277/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-140262352927184844624997235801727500000000000)
      constant := (5725158733583434698352879740470424580238714984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606973191817925898837/100000000000000000000)
  centralHi := (303486595908962949419/50000000000000000000)
  directionLo := (609020324752154162837/100000000000000000000)
  directionHi := (304510162376077081419/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree150.table
  base := (55646158740714780993291502771573833582189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-2846490351996463646124273104659347852500000000000)
      constant := (116961044262449916866576819047411521922247891061301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree150.table
  base := (111292317481425655829131215593945459738451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1129626212786409082204537592334880000000000000)
      constant := (46427136083940418178680106395592081568545525499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609020324752154162837/100000000000000000000)
  centralHi := (304510162376077081419/50000000000000000000)
  directionLo := (611060599561776666201/100000000000000000000)
  directionHi := (305530299780888333101/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree151.table
  base := (113594850247272352829750327536825315867843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-17192749520711847966991304504727448807500000000000)
      constant := (711291025166770971033371026234331542161683892549361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree151.table
  base := (113594850247269048968549299781651185583077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1137153602155339407409097298255940000000000000)
      constant := (47057266236958239859200487166521034423740648573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611060599561776666201/100000000000000000000)
  centralHi := (305530299780888333101/50000000000000000000)
  directionLo := (306547042357440070433/50000000000000000000)
  directionHi := (613094084714880140867/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree152.table
  base := (14489946263438416598505525801386736922091/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-2163319616180614257154621297687351312500000000000)
      constant := (90110029634476890438092954896207381016940883327657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree152.table
  base := (23183914021500907695322385553884816966161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1144680991524269732613657004177000000000000000)
      constant := (47691660327720962525219870938459016347227886445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306547042357440070433/50000000000000000000)
  centralHi := (613094084714880140867/100000000000000000000)
  directionLo := (307560423773912790439/50000000000000000000)
  directionHi := (615120847547825580879/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree153.table
  base := (118266477062136533214012564392418343026369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-5806788112725993382494212086090057397500000000000)
      constant := (243511300433944103442838025005628937835869908250921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree153.table
  base := (118266477062134169967447327226176969641043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1152208380893200057818216710098060000000000000)
      constant := (48330318356228609596974411789987410125420301307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307560423773912790439/50000000000000000000)
  centralHi := (615120847547825580879/100000000000000000000)
  directionLo := (308570477145632782381/50000000000000000000)
  directionHi := (617140954291265564763/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree154.table
  base := (60317785555581116411527416919234462817761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-8767085873455523118864151067520766942500000000000)
      constant := (370126008922411463024410003044195043238441152454747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree154.table
  base := (15079446388895029278550114707987062577151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-144966971282766297877847052002390000000000000)
      constant := (6121655040310150912711053428637368879445801799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308570477145632782381/50000000000000000000)
  centralHi := (617140954291265564763/100000000000000000000)
  directionLo := (123830894019079517627/20000000000000000000)
  directionHi := (77394308761924698517/12500000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree155.table
  base := (61513426127293452586940864242912348670579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-8823989577822056163986984005906447788750000000000)
      constant := (375017293352393699472799389659996696208613833018433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree155.table
  base := (123026852254585215036119828458843091129457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1167263159631060708227336121940180000000000000)
      constant := (49620426226478784076120750840022444550341153193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123830894019079517627/20000000000000000000)
  centralHi := (77394308761924698517/12500000000000000000)
  directionLo := (12423229181089612973/2000000000000000000)
  directionHi := (621161459054480648651/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree156.table
  base := (12544032049241317491636008978745182499987/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-2960297760729529736369938981430709545000000000000)
      constant := (126646934646954363909866347460193443696669461063415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree156.table
  base := (62720160246205872844335541211438074771573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-587395274499995516715947913930620000000000000)
      constant := (25135938034110685034450475683465434518059739277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12423229181089612973/2000000000000000000)
  centralHi := (621161459054480648651/100000000000000000000)
  directionLo := (623161984230641184711/100000000000000000000)
  directionHi := (77895248028830148089/12500000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree157.table
  base := (127875975824643781392767888040351781854733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-17875593973110244508465299765355618962500000000000)
      constant := (769793081375639753888179787720124879266309766843391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree157.table
  base := (127875975824642572847559966171791279698439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1182317938368921358636455533782300000000000000)
      constant := (50927589847708996726556603036288468361267428111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623161984230641184711/100000000000000000000)
  centralHi := (77895248028830148089/12500000000000000000)
  directionLo := (625156107676993383563/100000000000000000000)
  directionHi := (156289026919248345891/25000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree158.table
  base := (1629172728141019355061766317303113396457/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-2248675172730413824838870705265872581875000000000)
      constant := (97471125898316074894338276662239713644610578467390) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree158.table
  base := (65166909125640263254388566248522841603869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-594922663868925841920507619851680000000000000)
      constant := (25793783782470848224855901415952318013522696181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625156107676993383563/100000000000000000000)
  centralHi := (156289026919248345891/25000000000000000000)
  directionLo := (313571945230048920141/50000000000000000000)
  directionHi := (627143890460097840283/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree159.table
  base := (66406923886164679575022643180224954072471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-3017201465096062781492771919816390391250000000000)
      constant := (131634897552398869744139762873949490743766681934639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree159.table
  base := (132813847772328495111239243209311501820693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1197372717106782009045574945624420000000000000)
      constant := (52251809219919502308103707614849757384345114157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (313571945230048920141/50000000000000000000)
  centralHi := (627143890460097840283/100000000000000000000)
  directionLo := (629125392681781564123/100000000000000000000)
  directionHi := (157281348170445391031/25000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree160.table
  base := (67658032193895067743763699056087190234137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-9108508099654721389601148697834852020000000000000)
      constant := (399957107879617058859375235884969441310501365740099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree160.table
  base := (6765803219389470247497865621230367275079/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-301225026618928083562533662886370000000000000)
      constant := (13230078703160611951220974621434532374661897355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629125392681781564123/100000000000000000000)
  centralHi := (157281348170445391031/25000000000000000000)
  directionLo := (631100673500341390023/100000000000000000000)
  directionHi := (78887584187542673753/12500000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree161.table
  base := (68920234048833410417042038369065285849691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-9165411804021254434723981636220532866250000000000)
      constant := (405041749260525903274553561751086565827958561692857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree161.table
  base := (27568093619533240638961551133497124505363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1212427495844642659454694357466540000000000000)
      constant := (53593084343110566682200290525910352892309504935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631100673500341390023/100000000000000000000)
  centralHi := (78887584187542673753/12500000000000000000)
  directionLo := (158267447787787989581/25000000000000000000)
  directionHi := (25322791646046078333/4000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree162.table
  base := (140387058901962366096263258225397703764061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35615578680168608079928474540726230000000000000)
      linear := (-6148210338925191653231209716404142475000000000000)
      constant := (273439077866615598628463605835797339452074856054949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree162.table
  base := (70193529450980921963979280017606310944681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-609977442606786492329627031693800000000000000)
      constant := (27135058905661946380669812509821514654005652769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158267447787787989581/25000000000000000000)
  centralHi := (25322791646046078333/4000000000000000000)
  directionLo := (79379100370837321583/12500000000000000000)
  directionHi := (127006560593339714533/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree163.table
  base := (5718233472027188725803206872917976350287/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-18558438425508641049939295025983789117500000000000)
      constant := (830615420995619595958358683343907623820740588903725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree163.table
  base := (142955836800679276707232298741172582757167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1227482274582503309863813769308660000000000000)
      constant := (54951415217282459811789412607656194899986804983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79379100370837321583/12500000000000000000)
  centralHi := (127006560593339714533/20000000000000000000)
  directionLo := (636989765396054432297/100000000000000000000)
  directionHi := (318494882698027216149/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree164.table
  base := (72773400896910905208308719559847104053379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-9336122917120853570092480451377575405000000000000)
      constant := (420489030354185357336300132176121718428656820314033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree164.table
  base := (72773400896910718620919180669640704052629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57245000000000000000000000000000000000000000
      center := (1007512)
      previous := (503756)
      next := (503756)
      square := (3532590624892740337227581287515000000000000)
      linear := (-617504831975716817534186737614860000000000000)
      constant := (27818488280493150722242195795476316420698549421) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (636989765396054432297/100000000000000000000)
  centralHi := (318494882698027216149/50000000000000000000)
  directionLo := (31947036701191047941/5000000000000000000)
  directionHi := (638940734023820958821/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree165.table
  base := (74079976940695777644719746270787717717121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17807789340084304039964237270363115000000000000)
      linear := (-3131008873829128871738437796587752083750000000000)
      constant := (141900858789683442714456408665008454128049342696489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree165.table
  base := (148159953881391239833389555806907634493287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1242537053320363960272933181150780000000000000)
      constant := (56326801842435451025263727008065235507313642863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31947036701191047941/5000000000000000000)
  centralHi := (638940734023820958821/100000000000000000000)
  directionLo := (40055360224284324777/6250000000000000000)
  directionHi := (640885763588549196433/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree166.table
  base := (150795293063391837945810442977352638687223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1731432270000000000000000000000000000000000000000
      center := (30473207952)
      previous := (15236603976)
      next := (15236603976)
      square := (106846736040505824239785423622178690000000000000)
      linear := (-18899860651707839320676292656297874195000000000000)
      constant := (861896697084809920350540937582895153712395833888621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree166.table
  base := (37698823265847892822739654118843100134627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28622500000000000000000000000000000000000000
      center := (503756)
      previous := (251878)
      next := (251878)
      square := (1766295312446370168613790643757500000000000)
      linear := (-312516110672323571369373221767960000000000000)
      constant := (14255222765407485401301123148588324653441344523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40055360224284324777/6250000000000000000)
  centralHi := (640885763588549196433/100000000000000000000)
  directionLo := (642824908000659557627/100000000000000000000)
  directionHi := (160706227000164889407/25000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree167.table
  base := (76726409669912755735437157135939464067173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 865716135000000000000000000000000000000000000000
      center := (15236603976)
      previous := (7618301988)
      next := (7618301988)
      square := (53423368020252912119892711811089345000000000000)
      linear := (-9506834030220452705460979266534617943750000000000)
      constant := (436226346874249500428188231589519769271256502987271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree167.table
  base := (153452819339825286075829824461692890195579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1257591832058224610682052592992900000000000000)
      constant := (57719244218569805865033932084325551899849183971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642824908000659557627/100000000000000000000)
  centralHi := (160706227000164889407/25000000000000000000)
  directionLo := (128951644071975302179/20000000000000000000)
  directionHi := (40297388772492281931/6250000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree168.table
  base := (609892705901153878842086393695608862517/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4451947335021076009991059317590778750000000000)
      linear := (-796978144548915479215317683743358232500000000000)
      constant := (36794714280382016065387902684227844738400589038496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree168.table
  base := (9758283294418450154436850535033490864109/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14311250000000000000000000000000000000000000
      center := (251878)
      previous := (125939)
      next := (125939)
      square := (883147656223185084306895321878750000000000)
      linear := (-158139902678394366985826537364245000000000000)
      constant := (7302732664156884508909244637656516873806367882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell210.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128951644071975302179/20000000000000000000)
  centralHi := (40297388772492281931/6250000000000000000)
  directionLo := (646685752972194162019/100000000000000000000)
  directionHi := (32334287648609708101/5000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 97103
  qDenominator := 182328
  table := BinomialMassData.Q97103_182328.Degree169.table
  base := (3970860829400106515658974735047291065197/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 216429033750000000000000000000000000000000000000
      center := (3809150994)
      previous := (1904575497)
      next := (1904575497)
      square := (13355842005063228029973177952772336250000000000)
      linear := (-2405160359738379698926661285826494909062500000000)
      constant := (111719755503352319438236156362446629939061286103595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97103_182328.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 57
  qDenominator := 107
  table := BinomialMassData.Q57_107.Degree169.table
  base := (31766886635200819920695760758449512797637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 114490000000000000000000000000000000000000000
      center := (2015024)
      previous := (1007512)
      next := (1007512)
      square := (7065181249785480674455162575030000000000000)
      linear := (-1272646610796085261091172004835020000000000000)
      constant := (59128742345685784042150058165280992360100730065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q57_107.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell210.Kernel169
