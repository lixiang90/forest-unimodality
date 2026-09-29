import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell096.Parameters
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch000_049
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch050_099
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch000_049
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree000.table
  base := (77768286830451414195479743/2000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1194049343755025915925216400000000000000)
      linear := (-35383496012120446531923346000000000000)
      constant := (388841434152257070977398715000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree000.table
  base := (77768286830451414195479743/2000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1194049343755025915925216400000000000000)
      linear := (-35383496012120446531923346000000000000)
      constant := (388841434152257070977398715000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree001.table
  base := (219409644421299635920332284158995470366411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-3849937361594139954023177494157146000000000000)
      constant := (673721553898209763467725244904183754638886492411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree001.table
  base := (109508614455456608677080604946651028539383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-34727840519381573975413036969279314000000000000)
      constant := (6052706940372388562530880805624081591749982712894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4998515399417790539/10000000000000000000)
  directionHi := (49985153994177905391/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree002.table
  base := (64397438272695052008877132798637303930379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-7591388889031622606859031477554946000000000000)
      constant := (398819807895020167671031158111942561975691888758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree002.table
  base := (128377319236330318109756951575224233742413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-68479308531353232240140162341724514000000000000)
      constant := (3578018957197535574153290246745053060906248003717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4998515399417790539/10000000000000000000)
  centralHi := (49985153994177905391/100000000000000000000)
  directionLo := (70689682695874076313/100000000000000000000)
  directionHi := (35344841347937038157/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree003.table
  base := (39622926709467780155293173381816752025763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-11332840416469105259694885460952746000000000000)
      constant := (251737534585660561626244111851687687555482767526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree003.table
  base := (39453056288802123466584173943857133714333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-11358975171480543389429698634907746000000000000)
      constant := (250736386783972066907539002721525094650557384666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/100000000000000000000)
  centralHi := (35344841347937038157/50000000000000000000)
  directionLo := (43288413171035266727/50000000000000000000)
  directionHi := (17315365268414106691/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree004.table
  base := (51250901042897775055868409511911815020497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-15074291943906587912530739444350546000000000000)
      constant := (172651921977405733903218640927173370764658822497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree004.table
  base := (50998091265140887602480118961109690650989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-135982244555296548769594413086614914000000000000)
      constant := (1547537680922588577199986908909115009810606324901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43288413171035266727/50000000000000000000)
  centralHi := (17315365268414106691/20000000000000000000)
  directionLo := (99970307988355810781/100000000000000000000)
  directionHi := (49985153994177905391/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree005.table
  base := (4338377341383506848646344367762472831937/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-18815743471344070565366593427748346000000000000)
      constant := (130587159863339144131319824081270793221533391496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree005.table
  base := (4315441855542403205708686003063574644803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-169733712567268207034321538459060114000000000000)
      constant := (1171229959406311014499571149569962395566926281816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99970307988355810781/100000000000000000000)
  centralHi := (49985153994177905391/50000000000000000000)
  directionLo := (13971275274597115453/12500000000000000000)
  directionHi := (894161617574215389/800000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree006.table
  base := (24353665959019092318277923329729984249247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-22557194998781553218202447411146146000000000000)
      constant := (109414425735026144031907869583303112438175551247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree006.table
  base := (24219159430182343515292542098753491669839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-22609464508804429477672073759056146000000000000)
      constant := (109163245957133791790019831637131030213218043839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13971275274597115453/12500000000000000000)
  centralHi := (894161617574215389/800000000000000000)
  directionLo := (6121906100008819241/5000000000000000000)
  directionHi := (122438122000176384821/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree007.table
  base := (2180222799799761599985394157014020485659/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-26298646526219035871038301394543946000000000000)
      constant := (100705097876676736262609403616804585084407837272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree007.table
  base := (17340087471030125795202782554974948553621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-237236648591211523563775789203950514000000000000)
      constant := (905513267682412602477623685918255048163154856589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6121906100008819241/5000000000000000000)
  centralHi := (122438122000176384821/100000000000000000000)
  directionLo := (132248286713861650167/100000000000000000000)
  directionHi := (16531035839232706271/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree008.table
  base := (2503956923072519761632970599728309242279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-30040098053656518523874155377941746000000000000)
      constant := (100008620028546512513398000138677247325683281395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree008.table
  base := (12439715554896690775437758026324977839693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-270988116603183181828502914576395714000000000000)
      constant := (900444534041167315824267480443323987433289199237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132248286713861650167/100000000000000000000)
  centralHi := (16531035839232706271/12500000000000000000)
  directionLo := (70689682695874076313/50000000000000000000)
  directionHi := (141379365391748152627/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree009.table
  base := (1101212172497116674998615131007124717341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-33781549581094001176710009361339546000000000000)
      constant := (104939719357677457340947560787424954623937786728) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree009.table
  base := (2186012109407590029338714489887608584053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-33859953846128315565914448883204546000000000000)
      constant := (105100597884154406300944513879935980225260328212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/50000000000000000000)
  centralHi := (141379365391748152627/100000000000000000000)
  directionLo := (37488865495633429043/25000000000000000000)
  directionHi := (149955461982533716173/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree010.table
  base := (367823568597247481939326154407276609023/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-37523001108531483829545863344737346000000000000)
      constant := (114191225976421346434097279265748916848658032368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree010.table
  base := (728686559738486090753362897839287192579/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-338491052627126498357957165321286114000000000000)
      constant := (1030207161680063228071696682931511860764877273688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37488865495633429043/25000000000000000000)
  centralHi := (149955461982533716173/100000000000000000000)
  directionLo := (79033467907932513561/50000000000000000000)
  directionHi := (158066935815865027123/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree011.table
  base := (3504938503008321462274962038442634264877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-41264452635968966482381717328135146000000000000)
      constant := (127023359020722816350043815187114223598747146877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree011.table
  base := (345651915406547489011646973273171134311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-372242520639098156622684290693731314000000000000)
      constant := (1146740324026640390516995375605408916387179427990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79033467907932513561/50000000000000000000)
  centralHi := (158066935815865027123/100000000000000000000)
  directionLo := (41445500221705668219/25000000000000000000)
  directionHi := (165782000886822672877/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree012.table
  base := (1526348159587221089639389906787422879321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-45005904163406449135217571311532946000000000000)
      constant := (142998804230882749010499592647841247335421065321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree012.table
  base := (92722585467865681419623886210632071539/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-45110443183452201654156824007352946000000000000)
      constant := (143510940467085819042724946259233198271530328624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41445500221705668219/25000000000000000000)
  centralHi := (165782000886822672877/100000000000000000000)
  directionLo := (43288413171035266727/25000000000000000000)
  directionHi := (173153652684141066909/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree013.table
  base := (-34898758147826215229295810154990603043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-48747355690843931788053425294930746000000000000)
      constant := (161844684145655812581415482428865140124318235828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree013.table
  base := (-177758544064240325606219646924436887783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-439745456663041473152138541438621714000000000000)
      constant := (1462342888204395714449358633564968523198583907953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43288413171035266727/25000000000000000000)
  centralHi := (173153652684141066909/100000000000000000000)
  directionLo := (90112017868986032813/50000000000000000000)
  directionHi := (180224035737972065627/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree014.table
  base := (-775941195955282854474648516447499796977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-52488807218281414440889279278328546000000000000)
      constant := (183380131323887462305727946472778217349937442046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree014.table
  base := (-1586077934927908476677881818930988918617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-473496924675013131416865666811066914000000000000)
      constant := (1657355556345030462062990201665038367400782234447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90112017868986032813/50000000000000000000)
  centralHi := (180224035737972065627/100000000000000000000)
  directionLo := (46756830167837185011/25000000000000000000)
  directionHi := (37405464134269748009/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree015.table
  base := (-172001864955152303008654070152234771161/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-56230258745718897093725133261726346000000000000)
      constant := (207477857910545967314534070239814351130169645424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree015.table
  base := (-695679041468375430518142977179354961921/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-56360932520776087742399199131501346000000000000)
      constant := (208388477979195618651548871211728797029581008316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46756830167837185011/25000000000000000000)
  centralHi := (37405464134269748009/20000000000000000000)
  directionLo := (96795834488532086743/50000000000000000000)
  directionHi := (193591668977064173487/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree016.table
  base := (-471355540822667447860391484647518593977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-59971710273156379746560987245124146000000000000)
      constant := (234043409760377400014126918899431522746783392184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree016.table
  base := (-3798372305959676935613684390036899206111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-540999860698956447946319917555957314000000000000)
      constant := (2115918014219689832548012939767235716974480211001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96795834488532086743/50000000000000000000)
  centralHi := (193591668977064173487/100000000000000000000)
  directionLo := (199940615976711621563/100000000000000000000)
  directionHi := (49985153994177905391/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree017.table
  base := (-4632171443158767855195098094612912909733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12667669487897069942050620787600000000000000)
      linear := (-220460767476103330101719173801114000000000000)
      constant := (910047322742506887982022038736127106940642603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree017.table
  base := (-465683222304222087712023266856650538143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7447518)
      previous := (3723759)
      next := (3723759)
      square := (114009025391073629478455587088400000000000000)
      linear := (-1988758922875183758515733712555026000000000000)
      constant := (8228250332574854206099248456618318499675682170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199940615976711621563/100000000000000000000)
  centralHi := (49985153994177905391/25000000000000000000)
  directionLo := (103047034815379998333/50000000000000000000)
  directionHi := (206094069630759996667/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree018.table
  base := (-5355047658721538799908157470525377530819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-67454613328031345052232695211919746000000000000)
      constant := (294300291612009668110348874820652074965131415181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree018.table
  base := (-2688548873746981929988136426743885277109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-67611421858099973830641574255649746000000000000)
      constant := (295678995646418368209439663195408219992997057782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103047034815379998333/50000000000000000000)
  centralHi := (206094069630759996667/100000000000000000000)
  directionLo := (212069048087622228939/100000000000000000000)
  directionHi := (10603452404381111447/5000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree019.table
  base := (-2977498334291234386228451006774938206487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-71196064855468827705068549195317546000000000000)
      constant := (327885660113300142206181621244106801867945303026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree019.table
  base := (-2987335159176651576404064377811404459857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-642254264734871422740501293673292914000000000000)
      constant := (2964930111482248691938785237282435801064131606574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212069048087622228939/100000000000000000000)
  centralHi := (10603452404381111447/5000000000000000000)
  directionLo := (21788023493793995073/10000000000000000000)
  directionHi := (217880234937939950731/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree020.table
  base := (-1288971202533880283716223184124309526693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-74937516382906310357904403178715346000000000000)
      constant := (363720421866199604368620784377517584334248676535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree020.table
  base := (-3231185446446449166587100698595804999589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-676005732746843081005228419045738114000000000000)
      constant := (3289068016497212615887084893701231918958192275398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21788023493793995073/10000000000000000000)
  centralHi := (217880234937939950731/100000000000000000000)
  directionLo := (223540404393553847249/100000000000000000000)
  directionHi := (894161617574215389/400000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree021.table
  base := (-341766866831774895210726239481529238351/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-78678967910343793010740257162113146000000000000)
      constant := (401771734954423816809752395604027490973731912980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree021.table
  base := (-6850896853753698067061623425221396160761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-78861911195423859918883949379798146000000000000)
      constant := (403692165798865144941341000652088815149710613239) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223540404393553847249/100000000000000000000)
  centralHi := (894161617574215389/400000000000000000)
  directionLo := (114530375901172248339/50000000000000000000)
  directionHi := (229060751802344496679/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree022.table
  base := (-356771440466309135229248197630457961801/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-82420419437781275663576111145510946000000000000)
      constant := (442012041643304539243103436567790552173203443980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree022.table
  base := (-3574611446025212894726062210232177210299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-743508668770786397534682669790628514000000000000)
      constant := (3997166890852577859196340812898295977938829002618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114530375901172248339/50000000000000000000)
  centralHi := (229060751802344496679/100000000000000000000)
  directionLo := (117225577025746547391/50000000000000000000)
  directionHi := (234451154051493094783/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree023.table
  base := (-7352698768374124476735874194980394930369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-86161870965218758316411965128908746000000000000)
      constant := (484418137402091671933510060777258684663093715631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree023.table
  base := (-7364904065271207541300256594490902597339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-777260136782758055799409795163073714000000000000)
      constant := (4380671738161264412692666032472677830310904257949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117225577025746547391/50000000000000000000)
  centralHi := (234451154051493094783/100000000000000000000)
  directionLo := (119860188611459545793/50000000000000000000)
  directionHi := (239720377222919091587/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree024.table
  base := (-1498706741295468420780679068215529608161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-89903322492656240969247819112306546000000000000)
      constant := (528970441237786596286951380294885994029243829195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree024.table
  base := (-7504313658982144242323941316490466818641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-90112400532747746007126324503946546000000000000)
      constant := (531507574401841711787493340541026616243579875359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119860188611459545793/50000000000000000000)
  centralHi := (239720377222919091587/100000000000000000000)
  directionLo := (244876244000352769641/100000000000000000000)
  directionHi := (122438122000176384821/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree025.table
  base := (-1512665984984390739744144646023490462571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-93644774020093723622083673095704346000000000000)
      constant := (575652408085249772883975904044438748591334257145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree025.table
  base := (-757283491896140919902921856934089098523/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-844763072806701372328864045907964114000000000000)
      constant := (5205707639886058713157375484246090055085544512930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244876244000352769641/100000000000000000000)
  centralHi := (122438122000176384821/50000000000000000000)
  directionLo := (249925769970889526953/100000000000000000000)
  directionHi := (124962884985444763477/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree026.table
  base := (-7566650729970323323983084009238169587439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-97386225547531206274919527079102146000000000000)
      constant := (624450046842917487245689405863564583806742438561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree026.table
  base := (-7575018395145443226953632540521320939927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-878514540818673030593591171280409314000000000000)
      constant := (5646964581053813236610561956456032119291765902657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249925769970889526953/100000000000000000000)
  centralHi := (124962884985444763477/50000000000000000000)
  directionLo := (50975055121250693799/20000000000000000000)
  directionHi := (63718818901563367249/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree027.table
  base := (-7507356914297088850469848602280652640371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-101127677074968688927755381062499946000000000000)
      constant := (675351520316588506985644463720396521223969873629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree027.table
  base := (-3757356287208557605478110699605081023273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-101362889870071632095368699628094946000000000000)
      constant := (678581421993128523388042135391934810955127917454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975055121250693799/20000000000000000000)
  centralHi := (63718818901563367249/25000000000000000000)
  directionLo := (259730479026211600363/100000000000000000000)
  directionHi := (64932619756552900091/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree028.table
  base := (-3694357943392632839764646454708688854209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-104869128602406171580591235045897746000000000000)
      constant := (728346810627360098000291862356729848528612703582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree028.table
  base := (-924396642168264141973787545392534383497/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-946017476842616347123045422025299714000000000000)
      constant := (6586422453260148039424352427562276073511794644216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259730479026211600363/100000000000000000000)
  centralHi := (64932619756552900091/25000000000000000000)
  directionLo := (52899314685544660067/20000000000000000000)
  directionHi := (16531035839232706271/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree029.table
  base := (-7213493377445012303969075971755052541163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-108610580129843654233427089029295546000000000000)
      constant := (783427438044255384340524826344872358653741700837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree029.table
  base := (-7219154756478392257736575908133383017671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-979768944854588005387772547397744914000000000000)
      constant := (7084457534560762081151074462540437536809939266961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52899314685544660067/20000000000000000000)
  centralHi := (16531035839232706271/6250000000000000000)
  directionLo := (134589146084322771861/50000000000000000000)
  directionHi := (269178292168645543723/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree030.table
  base := (-3492015362793085629806244165069340072197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-112352031657281136886262943012693346000000000000)
      constant := (840586224018609049481666611063302731538607851606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree030.table
  base := (-3494494222192259291433782253572726041527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-112613379207395518183611074752243346000000000000)
      constant := (844585968873127502685098472139389166767904352946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134589146084322771861/50000000000000000000)
  centralHi := (269178292168645543723/100000000000000000000)
  directionLo := (273779963829806914273/100000000000000000000)
  directionHi := (136889981914903457137/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree031.table
  base := (-6702310135002294390515378222445107419023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-116093483184718619539098796996091146000000000000)
      constant := (899817091111607859676290141758842316708168062977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree031.table
  base := (-3353323419662610876546922894367546102299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1047271880878531321917226798142635314000000000000)
      constant := (8136816576154384050383340476238808026090492946618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273779963829806914273/100000000000000000000)
  centralHi := (136889981914903457137/50000000000000000000)
  directionLo := (139152779539677235359/50000000000000000000)
  directionHi := (278305559079354470719/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree032.table
  base := (-1592502457587746098126309956836250423347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-119834934712156102191934650979488946000000000000)
      constant := (961114893884773380401385625452192669463070698612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree032.table
  base := (-637379936814962106668627595725733422857/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1081023348890502980181953923515080514000000000000)
      constant := (8691040037269972220244877452952675551980831362870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139152779539677235359/50000000000000000000)
  centralHi := (278305559079354470719/100000000000000000000)
  directionLo := (70689682695874076313/25000000000000000000)
  directionHi := (282758730783496305253/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree033.table
  base := (-2994275354513727550236178493843307500551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-123576386239593584844770504962886746000000000000)
      constant := (1024475275865270988643965616990897206220006266898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree033.table
  base := (-2995929443084757215354873291939264436303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-123863868544719404271853449876391746000000000000)
      constant := (1029322790762524731610751933088590739598061131394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/25000000000000000000)
  centralHi := (282758730783496305253/100000000000000000000)
  directionLo := (143571424258202771101/50000000000000000000)
  directionHi := (287142848516405542203/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree034.table
  base := (-5559135816059800531721045067631975829873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12667669487897069942050620787600000000000000)
      linear := (-440546151443014074386181172824514000000000000)
      constant := (3771261413549624578266024457315293368420877343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree034.table
  base := (-5562021126420186785016274818810818940563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7447518)
      previous := (3723759)
      next := (3723759)
      square := (114009025391073629478455587088400000000000000)
      linear := (-3974139394167634244676152852110626000000000000)
      constant := (34101656816140131118308544259036758196736104197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143571424258202771101/50000000000000000000)
  centralHi := (287142848516405542203/100000000000000000000)
  directionLo := (291461028396485796619/100000000000000000000)
  directionHi := (14573051419824289831/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree035.table
  base := (-635347969314429387343072798314241305049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-131059289294468550150442212929682346000000000000)
      constant := (1157369588798461628170013175151507575255827687608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree035.table
  base := (-2542649037456629477249394530549008135069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1182277752926417954976135299632416114000000000000)
      constant := (10465433221524185607181400241866024404159665596758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291461028396485796619/100000000000000000000)
  centralHi := (14573051419824289831/5000000000000000000)
  directionLo := (59143231800015385803/20000000000000000000)
  directionHi := (36964519875009616127/12500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree036.table
  base := (-4560356967420087896847738585899674562603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-134800740821906032803278066913080146000000000000)
      constant := (1226897752461952035365428418927245917891384639397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree036.table
  base := (-4562546211218149611968743496054916189857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-135114357882043290360095825000540146000000000000)
      constant := (1232671632015204319053903658746428486906982248143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59143231800015385803/20000000000000000000)
  centralHi := (36964519875009616127/12500000000000000000)
  directionLo := (37488865495633429043/12500000000000000000)
  directionHi := (59982184793013486469/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree037.table
  base := (-3992585680638017728196619417867237160167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-138542192349343515456113920896477946000000000000)
      constant := (1298476800633082681353426717089357822499690817833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree037.table
  base := (-3994490406444098123869466035873902407509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1249780688950361271505589550377306514000000000000)
      constant := (11741193217602545495041575863018131207102074986419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37488865495633429043/12500000000000000000)
  centralHi := (59982184793013486469/20000000000000000000)
  directionLo := (304047821786971758143/100000000000000000000)
  directionHi := (4750747215421433721/1562500000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree038.table
  base := (-3380088173560673591095248100311368347091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-142283643876780998108949774879875746000000000000)
      constant := (1372104837666621104113758936147754767336450646909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree038.table
  base := (-3381744147481136777009028299057856083561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1283532156962332929770316675749751714000000000000)
      constant := (12406861881358540544918256535253235809709513013951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304047821786971758143/100000000000000000000)
  centralHi := (4750747215421433721/1562500000000000000)
  directionLo := (4814518487847983493/1562500000000000000)
  directionHi := (308129183222270943553/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree039.table
  base := (-1361693970704933572336960477208487229779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-146025095404218480761785628863273546000000000000)
      constant := (1447780258525693733877719928451387508390020712442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree039.table
  base := (-681206663202353571850868528034857952073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-146364847219367176448338200124688546000000000000)
      constant := (1454559594676156647902676643103270408936344919708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4814518487847983493/1562500000000000000)
  centralHi := (308129183222270943553/100000000000000000000)
  directionLo := (312157186643276718491/100000000000000000000)
  directionHi := (78039296660819179623/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree040.table
  base := (-1011464113055597057948656145397385378493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-149766546931655963414621482846671346000000000000)
      constant := (1525501704230113452220840275599249282064310167014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree040.table
  base := (-506044339481202180435929697714539720163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1351035092986276246299770926494642114000000000000)
      constant := (13793704503996125174823903903605970406123858786132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312157186643276718491/100000000000000000000)
  centralHi := (78039296660819179623/25000000000000000000)
  directionLo := (79033467907932513561/25000000000000000000)
  directionHi := (63226774326346010849/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree041.table
  base := (-639542159680330465378963958334054432241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-153507998459093446067457336830069146000000000000)
      constant := (1605268024135165011745020528793887485053389323518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree041.table
  base := (-320042043692314532332917460325301622409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1384786560998247904564498051867087314000000000000)
      constant := (14514856074549213530007819602842709085414125809276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79033467907932513561/25000000000000000000)
  centralHi := (63226774326346010849/20000000000000000000)
  directionLo := (320061151051933911147/100000000000000000000)
  directionHi := (80015287762983477787/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree042.table
  base := (-492173979521403464167031634692540641443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-157249449986530928720293190813466946000000000000)
      constant := (1687078243993389279494646878305096392700795120557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree042.table
  base := (-493113867312560549589717137758669767577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-157615336556691062536580575248836946000000000000)
      constant := (1694942486460539934871981456071886662733939150423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320061151051933911147/100000000000000000000)
  centralHi := (80015287762983477787/25000000000000000000)
  directionLo := (323940821806252962971/100000000000000000000)
  directionHi := (80985205451563240743/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree043.table
  base := (168766874221128368336930280868624937753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-160990901513968411373129044796864746000000000000)
      constant := (1770931538912656600641677928895611910355551271506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree043.table
  base := (168359583597138739848834510758878441931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1452289497022191221093952302611977714000000000000)
      constant := (16012576063814920976681260895548593104113099982758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323940821806252962971/100000000000000000000)
  centralHi := (80985205451563240743/25000000000000000000)
  directionLo := (10242955451393444301/3125000000000000000)
  directionHi := (327774574444590217633/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree044.table
  base := (1209811065150589534584650730443342136567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-164732353041405894025964898780262546000000000000)
      constant := (1856827210459840923205789363094618591434056558567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree044.table
  base := (1209105466288037895043012515981433927727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1486040965034162879358679427984422914000000000000)
      constant := (16789130910146159017095266988089899447634604187543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10242955451393444301/3125000000000000000)
  centralHi := (327774574444590217633/100000000000000000000)
  directionLo := (331564001773645345753/100000000000000000000)
  directionHi := (165782000886822672877/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree045.table
  base := (2124465093820328512233447076451928100339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-168473804568843376678800752763660346000000000000)
      constant := (1944764667274531875568175183326834945507567474339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree045.table
  base := (530963553084792873786118857021603481329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-168865825894014948624822950372985346000000000000)
      constant := (1953793516857242932862576183895288318181432781316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331564001773645345753/100000000000000000000)
  centralHi := (165782000886822672877/50000000000000000000)
  directionLo := (167655303295165385437/50000000000000000000)
  directionHi := (2682484852722646167/800000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree046.table
  base := (3081332526594408810122260968385609537011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-172215256096280859331636606747058146000000000000)
      constant := (2034743408654676389012549696950469238226085263011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree046.table
  base := (192550244318503216260214845165729590471/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1553543901058106195888133678729313314000000000000)
      constant := (18397603832192982255953748631134512074976369411824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167655303295165385437/50000000000000000000)
  centralHi := (2682484852722646167/800000000000000000)
  directionLo := (339015808645846562389/100000000000000000000)
  directionHi := (33901580864584656239/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree047.table
  base := (2040137545795200421669043983955638292613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-175956707623718341984472460730455946000000000000)
      constant := (2126763010658544662549140047444587716421579501226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree047.table
  base := (1019954469053991323367276512478347212551/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1587295369070077854152860804101758514000000000000)
      constant := (19229513680020939665950513351506533384153028827836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339015808645846562389/100000000000000000000)
  centralHi := (33901580864584656239/10000000000000000000)
  directionLo := (342680950931940382653/100000000000000000000)
  directionHi := (171340475465970191327/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree048.table
  base := (5121175714850479133642334128283815491259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-179698159151155824637308314713853746000000000000)
      constant := (2220823114337264929303841227529875914580015585259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree048.table
  base := (204831217443706799674720009915906973587/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-180116315231338834713065325497133746000000000000)
      constant := (2231096444798905650874130208809602725423117889675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342680950931940382653/100000000000000000000)
  centralHi := (171340475465970191327/50000000000000000000)
  directionLo := (346307305368282133817/100000000000000000000)
  directionHi := (173153652684141066909/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree049.table
  base := (1550983817666085473121399933102123568097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-183439610678593307290144168697251546000000000000)
      constant := (2316923415771310278282658989124321667347635880388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree049.table
  base := (6203593686604234564780609716005047492771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1654798305094021170682315054846648914000000000000)
      constant := (20948664100188582148852294289264449785560950408939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346307305368282133817/100000000000000000000)
  centralHi := (173153652684141066909/50000000000000000000)
  directionLo := (69979215591849067547/20000000000000000000)
  directionHi := (43737009744905667217/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree050.table
  base := (7328469830067664869157985573474736784393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-187181062206030789942980022680649346000000000000)
      constant := (2415063657634392162368592530549944541455685722393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree050.table
  base := (1832043692437661002107204633874906816293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1688549773105992828947042180219094114000000000000)
      constant := (21835899684631835402891492216775967984251801554548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69979215591849067547/20000000000000000000)
  centralHi := (43737009744905667217/12500000000000000000)
  directionLo := (70689682695874076313/20000000000000000000)
  directionHi := (176724206739685190783/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree051.table
  base := (8494708331146047006514436396775164677941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12667669487897069942050620787600000000000000)
      linear := (-660631535409924818670643171847914000000000000)
      constant := (8703265128202802650539910225781164222068276069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree051.table
  base := (4247226779992271865280348291538649514727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12667669487897069942050620787600000000000000)
      linear := (-662168873940009414537396887962914000000000000)
      constant := (8743395932900778849457891031038506065403477486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/20000000000000000000)
  centralHi := (176724206739685190783/50000000000000000000)
  directionLo := (44620674967389285099/12500000000000000000)
  directionHi := (356965399739114280793/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree052.table
  base := (9702590606481939788682412761789259263211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-194663965260905755248651730647444946000000000000)
      constant := (2617463124546601318027769841429582072690264189211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree052.table
  base := (388094828309865577970355185806958488631/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1756052709129936145476496430963984514000000000000)
      constant := (23665681873025579990048865068764642947947755291975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44620674967389285099/12500000000000000000)
  centralHi := (356965399739114280793/100000000000000000000)
  directionLo := (360448071475944131253/100000000000000000000)
  directionHi := (180224035737972065627/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree053.table
  base := (171126026765543419348322048672016145387/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-198405416788343237901487584630842746000000000000)
      constant := (2721722008930830264972221227022062336621451992768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree053.table
  base := (1368984497953291228233018988394943556557/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1789804177141907803741223556336429714000000000000)
      constant := (24608225453252989812683789258754589561433006936104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360448071475944131253/100000000000000000000)
  centralHi := (180224035737972065627/50000000000000000000)
  directionLo := (363897413910224166439/100000000000000000000)
  directionHi := (9097435347755604161/2500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree054.table
  base := (6121545258908814240743745956316738874573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-202146868315780720554323438614240546000000000000)
      constant := (2828020142957883649196405321929363814412359385146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree054.table
  base := (3060731719238651093603107697190821724519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-202617293905986606889550075745430546000000000000)
      constant := (2841022487679707998219328874811584360392787914076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363897413910224166439/100000000000000000000)
  centralHi := (9097435347755604161/2500000000000000000)
  directionLo := (183657183000264577231/50000000000000000000)
  directionHi := (367314366000529154463/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree055.table
  base := (13575628500960080949770577727409465918661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-205888319843218203207159292597638346000000000000)
      constant := (2936357414657434360491704157863050992416080544661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree055.table
  base := (6787743704867029330672937346276269631073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1857307113165851120270677807081320114000000000000)
      constant := (26548611687841542324003141929353521396372510083314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183657183000264577231/50000000000000000000)
  centralHi := (367314366000529154463/100000000000000000000)
  directionLo := (37069982342886591599/10000000000000000000)
  directionHi := (370699823428865915991/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree056.table
  base := (1868706092690521537906611286566303045143/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-209629771370655685859995146581036146000000000000)
      constant := (3046733729225978320520454187568116649621691865144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree056.table
  base := (2989905426563615024122852115048739803233/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1891058581177822778535404932453765314000000000000)
      constant := (27546452509211475025334187477794000791845348155485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37069982342886591599/10000000000000000000)
  centralHi := (370699823428865915991/100000000000000000000)
  directionLo := (46756830167837185011/12500000000000000000)
  directionHi := (374054641342697480089/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree057.table
  base := (16365125059334695420621049489439375074027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-213371222898093168512831000564433946000000000000)
      constant := (3159149006395072164073501466287684972916341856027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree057.table
  base := (16365020276335374156558304994763226082823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-213867783243310492977792450869578946000000000000)
      constant := (3173636015792567785551439765599063242933161400823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46756830167837185011/12500000000000000000)
  centralHi := (374054641342697480089/100000000000000000000)
  directionLo := (75475927375511120989/20000000000000000000)
  directionHi := (188689818438777802473/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree058.table
  base := (17822035288158910776374956213646740905039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-217112674425530651165666854547831746000000000000)
      constant := (3273603178203024145532923164667291814261590479039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree058.table
  base := (8910972515329543956354114290017267316189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1958561517201766095064859183198655714000000000000)
      constant := (29597425984791407379616215366952724930956650223402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75475927375511120989/20000000000000000000)
  centralHi := (188689818438777802473/50000000000000000000)
  directionLo := (76135118296265201431/20000000000000000000)
  directionHi := (95168897870331501789/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree059.table
  base := (19320360660343004492949059520112886839503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-220854125952968133818502708531229546000000000000)
      constant := (3390096187108188903896289425943894707662803037503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree059.table
  base := (19320282937861285479455955890116063200231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-1992312985213737753329586308571100914000000000000)
      constant := (30650557527858137507422856487287447609991743016079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76135118296265201431/20000000000000000000)
  centralHi := (95168897870331501789/25000000000000000000)
  directionLo := (19197162652946859709/5000000000000000000)
  directionHi := (383943253058937194181/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree060.table
  base := (10430042642892546161307555430090384058403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-224595577480405616471338562514627346000000000000)
      constant := (3508627984391498171958181192339062605226895312806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree060.table
  base := (20860018376676075977383840483384721198977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-225118272580634379066034825993727346000000000000)
      constant := (3524679815586660985451468088969641298580784680977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19197162652946859709/5000000000000000000)
  centralHi := (383943253058937194181/100000000000000000000)
  directionLo := (96795834488532086743/25000000000000000000)
  directionHi := (387183337954128346973/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree061.table
  base := (11220597855391474727061926165799580258203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-228337029007843099124174416498025146000000000000)
      constant := (3629198528803887474745083427875235351242461312406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree061.table
  base := (2244113812660301707968118773583269240919/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2059815921237681069859040559315991314000000000000)
      constant := (32812108057250233274467289058519573865833420542710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96795834488532086743/25000000000000000000)
  centralHi := (387183337954128346973/100000000000000000000)
  directionLo := (19519826639158609849/5000000000000000000)
  directionHi := (390396532783172196981/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree062.table
  base := (12031840272255816557823786490685319908041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-232078480535280581777010270481422946000000000000)
      constant := (3751807785421076146893629598942811890046747228082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree062.table
  base := (24063630998990331659743920151527411023219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2093567389249652728123767684688436514000000000000)
      constant := (33920526370029232887737578206806393461521404294971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19519826639158609849/5000000000000000000)
  centralHi := (390396532783172196981/100000000000000000000)
  directionLo := (393583496133849752841/100000000000000000000)
  directionHi := (196791748066924876421/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree063.table
  base := (6431882535690822712957666612035607709691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-235819932062718064429846124464820746000000000000)
      constant := (3876455724673913268567846961082278251594081262764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree063.table
  base := (6281124883985833332237636762165502879/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-236368761917958265154277201117875746000000000000)
      constant := (3894152557480932466615015422962179173593349136384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393583496133849752841/100000000000000000000)
  centralHi := (196791748066924876421/50000000000000000000)
  directionLo := (198372430070792475251/50000000000000000000)
  directionHi := (396744860141584950503/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree064.table
  base := (13716368170085406096466765230633653430011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-239561383590155547082681978448218546000000000000)
      constant := (4003142321527375113700403423992227768100134312022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree064.table
  base := (5486539938077201635063435455062413666599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2161070325273596044653221935433326914000000000000)
      constant := (36192647778018596494525989740159277587389279026955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198372430070792475251/50000000000000000000)
  centralHi := (396744860141584950503/100000000000000000000)
  directionLo := (199940615976711621563/50000000000000000000)
  directionHi := (399881231953423243127/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree065.table
  base := (14589646111741349237524363407066655718917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-243302835117593029735517832431616346000000000000)
      constant := (4131867554785425674136260118223749974501710481834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree065.table
  base := (29179260713788211206398467301130711844663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2194821793285567702917949060805772114000000000000)
      constant := (37356350464958870978779861683539635857818037423967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199940615976711621563/50000000000000000000)
  centralHi := (399881231953423243127/100000000000000000000)
  directionLo := (16119727803578280599/4000000000000000000)
  directionHi := (6296768673272765859/1562500000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree066.table
  base := (15483595969797972804642998262493736140313/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-247044286645030512388353686415014146000000000000)
      constant := (4262631406502445286235875420848531275999871596626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree066.table
  base := (30967164855511549340588756449343780139379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-247619251255282151242519576242024146000000000000)
      constant := (4282053435530374721104059203232806465251116153379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16119727803578280599/4000000000000000000)
  centralHi := (6296768673272765859/1562500000000000000)
  directionLo := (203040655355171936177/50000000000000000000)
  directionHi := (81216262142068774471/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree067.table
  base := (1024888454156827582304540717435344350849/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-250785738172467995041189540398411946000000000000)
      constant := (4395433861484890304937992857640869407381516315168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree067.table
  base := (4099550907287617340897739977707849026363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2262324729309511019447403311550662514000000000000)
      constant := (39739039008430960528923863710027648146232814874136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203040655355171936177/50000000000000000000)
  centralHi := (81216262142068774471/20000000000000000000)
  directionLo := (409146118798715381857/100000000000000000000)
  directionHi := (204573059399357690929/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree068.table
  base := (693340076164991237345872971184876378391/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12667669487897069942050620787600000000000000)
      linear := (-880716919376835562955105170871314000000000000)
      constant := (15675691719271111565230141788816819674917505950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree068.table
  base := (8666745952892016886719380833242762655347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7447518)
      previous := (3723759)
      next := (3723759)
      square := (114009025391073629478455587088400000000000000)
      linear := (-7944900336752535216996991131221826000000000000)
      constant := (141723268572678284512474988839059476884380747628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409146118798715381857/100000000000000000000)
  centralHi := (204573059399357690929/50000000000000000000)
  directionLo := (103047034815379998333/25000000000000000000)
  directionHi := (412188139261519993333/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree069.table
  base := (18289454106629063258916396161842912631067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-258268641227342960346861248365207546000000000000)
      constant := (4667154531765297326320799779809798725439528106134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree069.table
  base := (9144722759161450414640558224481094713867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-258869740592606037330761951366172546000000000000)
      constant := (4688381961222465707554074267967320692495243743468) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103047034815379998333/25000000000000000000)
  centralHi := (412188139261519993333/100000000000000000000)
  directionLo := (103801968239918227719/25000000000000000000)
  directionHi := (415207872959672910877/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree070.table
  base := (38532140740824785190010206158379319053431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-262010092754780442999697102348605346000000000000)
      constant := (4806072726952590895608317019680791745597138499431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree070.table
  base := (7706425197934979369534551636704941365789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2363579133345425994241584687667998114000000000000)
      constant := (43451278027692583480978196257162378641960269790505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103801968239918227719/25000000000000000000)
  centralHi := (415207872959672910877/100000000000000000000)
  directionLo := (41820580267078738683/10000000000000000000)
  directionHi := (418205802670787386831/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree071.table
  base := (10131674711252213402183128111725258011427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-265751544282217925652532956332003146000000000000)
      constant := (4947029484625375266285942125715708589653172773708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree071.table
  base := (3957684197208363449454777324134930689/976562500000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2397330601357397652506311813040443314000000000000)
      constant := (44725545678831854357759339386622997812181616138240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41820580267078738683/10000000000000000000)
  centralHi := (418205802670787386831/100000000000000000000)
  directionLo := (21059119699511375707/5000000000000000000)
  directionHi := (421182393990227514141/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree072.table
  base := (42562580370421744079186940537488134379393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-269492995809655408305368810315400946000000000000)
      constant := (5090024798175226873092791448283473769495353317393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree072.table
  base := (42562569497677371894626313540532026453501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-270120229929929923419004326490320946000000000000)
      constant := (5113137838471859710615666595662246245638460519501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21059119699511375707/5000000000000000000)
  centralHi := (421182393990227514141/100000000000000000000)
  directionLo := (424138096175244457879/100000000000000000000)
  directionHi := (10603452404381111447/2500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree073.table
  base := (22319891746171722547673573125288878716119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-273234447337092890958204664298798746000000000000)
      constant := (5235058662007552336031376710103203350364999140238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree073.table
  base := (11159943540116785713070579211344394933811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2464833537381340969035766063785333714000000000000)
      constant := (47329362580709549663468033701021824140612540553196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424138096175244457879/100000000000000000000)
  centralHi := (10603452404381111447/2500000000000000000)
  directionLo := (427073342936529576179/100000000000000000000)
  directionHi := (21353667146826478809/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree074.table
  base := (9351661333203960630750018519017283249473/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-276975898864530373611040518282196546000000000000)
      constant := (5382131071386133875705926736297198376300837337365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree074.table
  base := (23379149329072527613013154408399161808941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2498585005393312627300493189157778914000000000000)
      constant := (48658911740563329379601266297551726079096748468938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427073342936529576179/100000000000000000000)
  centralHi := (21353667146826478809/5000000000000000000)
  directionLo := (85997710636226654437/20000000000000000000)
  directionHi := (214994276590566636093/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree075.table
  base := (48918148583733149841093199772154672871581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-280717350391967856263876372265594346000000000000)
      constant := (5531242022301507813043587403899576011678940217581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree075.table
  base := (48918141713266110985049288752628274908489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-281370719267253809507246701614469346000000000000)
      constant := (5556320887839805307919285700877038618497702182489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85997710636226654437/20000000000000000000)
  centralHi := (214994276590566636093/50000000000000000000)
  directionLo := (54110516463794083409/12500000000000000000)
  directionHi := (432884131710352667273/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree076.table
  base := (51119308138454582659213790084745242114557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-284458801919405338916712226248992146000000000000)
      constant := (5682391511359522425956089444928542243068473876557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree076.table
  base := (408954417959120665753060841584200654263/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2566087941417255943829947439902669314000000000000)
      constant := (51373291300866830488662333071833905652942388795875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54110516463794083409/12500000000000000000)
  centralHi := (432884131710352667273/100000000000000000000)
  directionLo := (435760469875879901461/100000000000000000000)
  directionHi := (217880234937939950731/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree077.table
  base := (53361784393068896561579084645811263393843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-288200253446842821569548080232389946000000000000)
      constant := (5835579535686981558655558312783632508876786031843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree077.table
  base := (213447117353510657891558734217232959131/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2599839409429227602094674565275114514000000000000)
      constant := (52758121646250512250089847351418239110339361544750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435760469875879901461/100000000000000000000)
  centralHi := (217880234937939950731/50000000000000000000)
  directionLo := (342670270466579849/78125000000000000)
  directionHi := (438617946197222206721/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree078.table
  base := (11129115310863569093724920147608991754071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-291941704974280304222383934215787746000000000000)
      constant := (5990806092851754635403803223889098444634867200355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree078.table
  base := (55645572219828162376128094201535021452541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-292621208604577695595489076738617746000000000000)
      constant := (6017931000594918931687421434664642415308512158541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342670270466579849/78125000000000000)
  centralHi := (438617946197222206721/100000000000000000000)
  directionLo := (441456926943151492193/100000000000000000000)
  directionHi := (220728463471575746097/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree079.table
  base := (14492670987684595611207129322362996258101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-295683156501717786875219788199185546000000000000)
      constant := (6148071180795135282833467339316384322061335696404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree079.table
  base := (5797068023444550491211417455953698178339/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2667342345453170918624128816020004914000000000000)
      constant := (55583063360109656189558772917684402242163699710510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441456926943151492193/100000000000000000000)
  centralHi := (220728463471575746097/50000000000000000000)
  directionLo := (444277766679712066469/100000000000000000000)
  directionHi := (44427776667971206647/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree080.table
  base := (15084276503495854733405340743425000646221/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-299424608029155269528055642182583346000000000000)
      constant := (6307374797774570759083020103409483861625256928884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree080.table
  base := (30168551414114456788746486136322475383949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2701093813465142576888855941392450114000000000000)
      constant := (57023174695229567195177204283029194345293934323082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444277766679712066469/100000000000000000000)
  centralHi := (44427776667971206647/10000000000000000000)
  directionLo := (447080808787107694499/100000000000000000000)
  directionHi := (894161617574215389/200000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree081.table
  base := (62744842263006535363628307689209088514191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-303166059556592752180891496165981146000000000000)
      constant := (6468716942315172260700206715702122918093598120191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree081.table
  base := (31372419766238679163265096843386619185627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-303871697941901581683731451862766146000000000000)
      constant := (6497968110864518106738980499701852736619503135254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447080808787107694499/100000000000000000000)
  centralHi := (894161617574215389/200000000000000000)
  directionLo := (112466596486900287129/25000000000000000000)
  directionHi := (449866385947601148517/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree082.table
  base := (16298473072667893406884433470291877860079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-306907511084030234833727350149378946000000000000)
      constant := (6632097613168659919791851649459631168243520296316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree082.table
  base := (65193889950675411181033879134954194982059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2768596749489085893418310192137340514000000000000)
      constant := (59958678256821493197710552821768900768922690884531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112466596486900287129/25000000000000000000)
  centralHi := (449866385947601148517/100000000000000000000)
  directionLo := (113158705151597183561/25000000000000000000)
  directionHi := (90526964121277746849/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree083.table
  base := (67684255752415352951449300508931395152299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-310648962611467717486563204132776746000000000000)
      constant := (6797516809278602679541995685151053446968343886299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree083.table
  base := (3384212687369727787222896943475417395159/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2802348217501057551683037317509785714000000000000)
      constant := (61454070463096240406053448886973597664615480048620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113158705151597183561/25000000000000000000)
  centralHi := (90526964121277746849/20000000000000000000)
  directionLo := (455386425407257161607/100000000000000000000)
  directionHi := (56923303175907145201/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree084.table
  base := (4388495772290546425776437648788684225641/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-314390414138905200139399058116174546000000000000)
      constant := (6964974529750987974178174243918074987991992506256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree084.table
  base := (70215930638900241092925429333274544321799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-315122187279225467771973826986914546000000000000)
      constant := (6996432178752836759319454888613552050165180055799) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455386425407257161607/100000000000000000000)
  centralHi := (56923303175907145201/12500000000000000000)
  directionLo := (458121503604688993357/100000000000000000000)
  directionHi := (229060751802344496679/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree085.table
  base := (36394460928314790855641094088896089201697/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (827502)
      previous := (413751)
      next := (413751)
      square := (12667669487897069942050620787600000000000000)
      linear := (-1100802303343746307239567169894714000000000000)
      constant := (24686750082454339411078720462428074720681606946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree085.table
  base := (36394460192601279666264173533352586344229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (7447518)
      previous := (3723759)
      next := (3723759)
      square := (114009025391073629478455587088400000000000000)
      linear := (-9930280808044985703157410270777426000000000000)
      constant := (223183860509470867829902490175706661593466658298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458121503604688993357/100000000000000000000)
  centralHi := (229060751802344496679/50000000000000000000)
  directionLo := (46084034945395433521/10000000000000000000)
  directionHi := (460840349453954335211/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree086.table
  base := (18850806010895447037589423044357724900917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-321873317193780165445070766082970146000000000000)
      constant := (7306005540873443351764788434546023646615745691668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree086.table
  base := (1885080569583217604372340417332664883019/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2903602621536972526477218693627121314000000000000)
      constant := (66050808692880056869477002639448724085040409326840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46084034945395433521/10000000000000000000)
  centralHi := (460840349453954335211/100000000000000000000)
  directionLo := (463543248580609174157/100000000000000000000)
  directionHi := (231771624290304587079/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree087.table
  base := (15611767748173920831733523482469041997641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-325614768721217648097906620066367946000000000000)
      constant := (7479578830341840349492500439547703940669046518205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree087.table
  base := (4878677353851841053193172689674169909647/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-326372676616549353860216202111062946000000000000)
      constant := (7513323180107552105136422942342932940874361786352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463543248580609174157/100000000000000000000)
  centralHi := (231771624290304587079/50000000000000000000)
  directionLo := (233115239165356856213/50000000000000000000)
  directionHi := (466230478330713712427/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree088.table
  base := (80755765799065202356330677830232218144843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-329356220248655130750742474049765746000000000000)
      constant := (7655190641776349214810342825729107759064306782843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree088.table
  base := (80755764874960796559203124968856173781181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-2971105557560915843006672944372011714000000000000)
      constant := (69207435467495711616789955621433839411023472544629) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233115239165356856213/50000000000000000000)
  centralHi := (466230478330713712427/100000000000000000000)
  directionLo := (93780461620597237913/20000000000000000000)
  directionHi := (234451154051493094783/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree089.table
  base := (83494005091772687862716827535940130352151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-333097671776092613403578328033163546000000000000)
      constant := (7832840974789440007618408991745653807099825318151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree089.table
  base := (83494004300606150297172130051593758668241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-3004857025572887501271400069744456914000000000000)
      constant := (70813389229077042661295488793946339262035270168169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93780461620597237913/20000000000000000000)
  centralHi := (234451154051493094783/50000000000000000000)
  directionLo := (471558999664018147533/100000000000000000000)
  directionHi := (235779499832009073767/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree090.table
  base := (86273556512092524701987047121000951659429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-336839123303530096056414182016561346000000000000)
      constant := (8012529829053358643715240528251959803788760973429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree090.table
  base := (8627355583482546256934389918323703580093/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-337623165953873239948458577235211346000000000000)
      constant := (8048641100316595339415203710873348825002687180930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471558999664018147533/100000000000000000000)
  centralHi := (235779499832009073767/50000000000000000000)
  directionLo := (237100403723797540683/50000000000000000000)
  directionHi := (474200807447595081367/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree091.table
  base := (11136802496203524448839694201052250811439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-340580574830967578709250035999959146000000000000)
      constant := (8194257204290949310713342833216770964820982283512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree091.table
  base := (22273604847483688900234765924949681006407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-3072359961596830817800854320489347314000000000000)
      constant := (74080577486393105325240927561246856887951695262652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237100403723797540683/50000000000000000000)
  centralHi := (474200807447595081367/100000000000000000000)
  directionLo := (119206994709772805501/25000000000000000000)
  directionHi := (95365595767818244401/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree092.table
  base := (22989148846987989400104767841346371062131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-344322026358405061362085889983356946000000000000)
      constant := (8378023100267884472366224859060629042091458832524) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree092.table
  base := (22989148722958663322546595262110209740971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-3106111429608802476065581445861792514000000000000)
      constant := (75741811977663585621761110701162297334336965770956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119206994709772805501/25000000000000000000)
  centralHi := (95365595767818244401/20000000000000000000)
  directionLo := (479440754445838183173/100000000000000000000)
  directionHi := (239720377222919091587/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree093.table
  base := (47430041351229651007598315856303357588593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-348063477885842544014921743966754746000000000000)
      constant := (8563827516786086640346443915917841766839967453186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree093.table
  base := (9486008227791887013824538993106821079973/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-348873655291197126036700952359359746000000000000)
      constant := (8602385930548137837642867737664741218380182979730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479440754445838183173/100000000000000000000)
  centralHi := (239720377222919091587/50000000000000000000)
  directionLo := (482039368354303801269/100000000000000000000)
  directionHi := (48203936835430380127/10000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree094.table
  base := (19560976371710503707685310787512600681869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-351804929413280026667757597950152546000000000000)
      constant := (8751670453678159180286841502100146105016055179345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree094.table
  base := (9780488149530426933230122060168501748273/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-3173614365632745792595035696606682914000000000000)
      constant := (79119561676742812323153979543603141353583608964570) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482039368354303801269/100000000000000000000)
  centralHi := (48203936835430380127/10000000000000000000)
  directionLo := (121156012093714798559/25000000000000000000)
  directionHi := (484624048374859194237/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree095.table
  base := (12598874101262862674165669137547051122199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-355546380940717509320593451933550346000000000000)
      constant := (8941551910802671434147093675998391352801706049592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree095.table
  base := (100790992499333067822524001166135869737383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-3207365833644717450859762821979128114000000000000)
      constant := (80836076881860013707468567481507537639756174138447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121156012093714798559/25000000000000000000)
  centralHi := (484624048374859194237/100000000000000000000)
  directionLo := (487195016274858402651/100000000000000000000)
  directionHi := (121798754068714600663/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree096.table
  base := (103818415518148871440432969357317933832589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-359287832468154991973429305916948146000000000000)
      constant := (9133471888040167161324036754671644558448651706589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree096.table
  base := (51909207626152680490700155690580317008549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-360124144628521012124943327483508146000000000000)
      constant := (9174557665471617020459869609653617501057056485098) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487195016274858402651/100000000000000000000)
  centralHi := (121798754068714600663/25000000000000000000)
  directionLo := (489752488000705539283/100000000000000000000)
  directionHi := (122438122000176384821/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree097.table
  base := (106887149949793838948465553940089562471107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-363029283995592474626265159900345946000000000000)
      constant := (9327430385289785384804964726512455238125976533107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree097.table
  base := (106887149722406567148115051226450583921119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-3274868769668660767389217072724018514000000000000)
      constant := (84324387998018538900484989742431901783774612976071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell096.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489752488000705539283/100000000000000000000)
  centralHi := (122438122000176384821/25000000000000000000)
  directionLo := (492296673889538789201/100000000000000000000)
  directionHi := (246148336944769394601/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree098.table
  base := (109997196077273177930752812889930307466043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (239148078)
      previous := (119574039)
      next := (119574039)
      square := (3660956482002253213252629407616400000000000000)
      linear := (-366770735523029957279101013883743746000000000000)
      constant := (9523427402466399733550120483572968245621195304043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree098.table
  base := (109997195882799832367400943296365808143921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 275940090000000000000000000000000000000000000000
      center := (2152332702)
      previous := (1076166351)
      next := (1076166351)
      square := (32948608338020278919273664668547600000000000000)
      linear := (-3308620237680632425653944198096463714000000000000)
      constant := (86096183907441434466933726398018846099215629369289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell096.Kernel098
