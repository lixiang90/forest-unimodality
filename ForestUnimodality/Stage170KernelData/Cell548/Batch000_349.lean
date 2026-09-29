import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell548.Parameters
import ForestUnimodality.BinomialMassData.Q33_53.Batch000_049
import ForestUnimodality.BinomialMassData.Q33_53.Batch050_099
import ForestUnimodality.BinomialMassData.Q467_742.Batch000_049
import ForestUnimodality.BinomialMassData.Q467_742.Batch050_099

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree000.table
  base := (1198493691166624768417392521/100000000000000000000000000)
  polynomial :=
    { denominator := 16562500000000000000000000000000000000000
      center := (33)
      previous := (0)
      next := (20)
      square := (409976162852472663083308603125000000000)
      linear := (-1089671862675318293224580032500000000000)
      constant := (198500517599472227269130636290625000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree000.table
  base := (1198493691166624768417392521/100000000000000000000000000)
  polynomial :=
    { denominator := 231875000000000000000000000000000000000000
      center := (467)
      previous := (0)
      next := (275)
      square := (5739666279934617283166320443750000000000)
      linear := (-15255406077454456105144120455000000000000)
      constant := (2779007246392611181767828908068750000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree001.table
  base := (97008753948446661017889848908453081204001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-2713953135041762089740835504920000000000000)
      constant := (273917846522946957244503914517064705102038809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree001.table
  base := (12095535856421458210757415135625368304139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (4258832379711486024109409769262500000000000)
      linear := (-16680359614930138972494280672072500000000000)
      constant := (1673652930949619290977004731688811943749996099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48297080828003564581/100000000000000000000)
  directionHi := (24148540414001782291/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree002.table
  base := (78384506386507554326591870134545255047551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-3579822790986184354172783274720000000000000)
      constant := (223561718192770593649111565912177621428570759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree002.table
  base := (38993697807738620914336814322256153508039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-88164831681556286059886495866140000000000000)
      constant := (5451117845024195455503708706208989224999995999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48297080828003564581/100000000000000000000)
  centralHi := (24148540414001782291/50000000000000000000)
  directionLo := (4268899170624514509/6250000000000000000)
  directionHi := (13660477345998446429/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree003.table
  base := (63204772803672998113535639215799217946067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-4445692446930606618604731044520000000000000)
      constant := (183420356019449213002312631870240003210502203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree003.table
  base := (62720974428242711814410268179773104606491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-219216449806784032459591738087980000000000000)
      constant := (8925424628431298028884654678859314891142027731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4268899170624514509/6250000000000000000)
  centralHi := (13660477345998446429/20000000000000000000)
  directionLo := (83652997851362914859/100000000000000000000)
  directionHi := (4182649892568145743/5000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree004.table
  base := (25413900712149842089891452700210376748407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-2655781051437514441518339407160000000000000)
      constant := (75845539632600381286644783014730948286275263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree004.table
  base := (50303881582435751347580859301468159553217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-262103236250455492799410484443680000000000000)
      constant := (7367790057020511333064905287668498949064341097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83652997851362914859/100000000000000000000)
  centralHi := (4182649892568145743/5000000000000000000)
  directionLo := (96594161656007129163/100000000000000000000)
  directionHi := (24148540414001782291/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree005.table
  base := (20361201522551862130638393197144880577067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-3088715879409725573734313292060000000000000)
      constant := (63440888729000400114153293012829969540981203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree005.table
  base := (10047623680028572339411411577105692532159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-76247505673531738284807307699845000000000000)
      constant := (1538557992211631554832001681095035875818896919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96594161656007129163/100000000000000000000)
  centralHi := (24148540414001782291/25000000000000000000)
  directionLo := (107995555846217798967/100000000000000000000)
  directionHi := (13499444480777224871/12500000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree006.table
  base := (16232978673566205761749223711827111417519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-3521650707381936705950287176960000000000000)
      constant := (53902655060955586234600142489682355971810871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree006.table
  base := (15973769605629394852490761637915407205277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-173938404568899206739523988577540000000000000)
      constant := (2612557005279411856940047533199004563141531557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107995555846217798967/100000000000000000000)
  centralHi := (13499444480777224871/12500000000000000000)
  directionLo := (118303204094564813693/100000000000000000000)
  directionHi := (59151602047282406847/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree007.table
  base := (12857083297692039978361101714774943629663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-3954585535354147838166261061860000000000000)
      constant := (46747272459656099737325606779972816655723367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree007.table
  base := (25222931538704807297556813023392629073669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (396016)
      previous := (0)
      next := (233200)
      square := (4867237005384555456125039736300000000000000)
      linear := (-55823370797352839116980960501540000000000000)
      constant := (647425007824481775686976890706924265475553547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118303204094564813693/100000000000000000000)
  centralHi := (59151602047282406847/50000000000000000000)
  directionLo := (63891032460641466737/50000000000000000000)
  directionHi := (5111282596851317339/4000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree008.table
  base := (10093443252260505648523957003041851785621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-4387520363326358970382234946760000000000000)
      constant := (41581278276345115320681938683624561665809389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree008.table
  base := (19730908493093853749997301723738369856673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-433650382025141334158685469866480000000000000)
      constant := (4035482367584860667262944064618512965442328393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63891032460641466737/50000000000000000000)
  centralHi := (5111282596851317339/4000000000000000000)
  directionLo := (4268899170624514509/3125000000000000000)
  directionHi := (136604773459984464289/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree009.table
  base := (15656246754571254283604759156188631795021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-9640910382597140205196417663320000000000000)
      constant := (76169257293244054877552143029513866712213989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree009.table
  base := (476237762489041516755558782796835283939/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 86025625000000000000000000000000000000000000
      center := (173257)
      previous := (0)
      next := (102025)
      square := (2129416189855743012054704884631250000000000)
      linear := (-29783573029300799656156513513886250000000000)
      constant := (231482642263835147076626657507543723133295798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4268899170624514509/3125000000000000000)
  centralHi := (136604773459984464289/100000000000000000000)
  directionLo := (28978248496802138749/20000000000000000000)
  directionHi := (72445621242005346873/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree010.table
  base := (2984229647943047191953238862996004640123/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-2626695009635390617407091358280000000000000)
      constant := (17998514667913618046463849724455777034105507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree010.table
  base := (1156092556751164911515199706861435429957/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-259711977456242127419161481288940000000000000)
      constant := (1755401862642636843589830485846224170073557185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28978248496802138749/20000000000000000000)
  centralHi := (72445621242005346873/50000000000000000000)
  directionLo := (38182194938435551221/25000000000000000000)
  directionHi := (30545755950748440977/20000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree011.table
  base := (8878180409274213395174732384642535645239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-11372649694485984734060313202920000000000000)
      constant := (70213583694280952361489407612880882627476351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree011.table
  base := (2135565124630004099125819840903034196753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-140577685339038928794535427233395000000000000)
      constant := (858930691812561030379961944675585779875279673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38182194938435551221/25000000000000000000)
  centralHi := (30545755950748440977/20000000000000000000)
  directionLo := (160183295575955123739/100000000000000000000)
  directionHi := (8009164778797756187/5000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree012.table
  base := (6357458609698546897800395798436697260379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-12238519350430406998492260972720000000000000)
      constant := (70483523126086498822952018291248682604404611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree012.table
  base := (6059821002243846901806335034179281127827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-605197527799827175517960455289280000000000000)
      constant := (3461440521233217715692637436958430433715236107) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160183295575955123739/100000000000000000000)
  centralHi := (8009164778797756187/5000000000000000000)
  directionLo := (83652997851362914859/50000000000000000000)
  directionHi := (167305995702725829719/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree013.table
  base := (534384036442383846094224021654416948847/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (6996)
      previous := (0)
      next := (4240)
      square := (86914946524724204573661423862500000000000)
      linear := (-1638048625796853657865526092815000000000000)
      constant := (9065484164342553085532446961859757209311223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree013.table
  base := (4013185477104402879921161957507489372353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-648084314243498635857779201644980000000000000)
      constant := (3574134857571295426893368914275253344700039273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83652997851362914859/50000000000000000000)
  centralHi := (167305995702725829719/100000000000000000000)
  directionLo := (1393100811044765091/800000000000000000)
  directionHi := (21767200172574454547/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree014.table
  base := (254995839216353879654825166810652313451/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-6985129331159625763678078256160000000000000)
      constant := (38053464058654375168673012120295611742419295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree014.table
  base := (2320891532280342726247432806584701680521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (396016)
      previous := (0)
      next := (233200)
      square := (4867237005384555456125039736300000000000000)
      linear := (-98710157241024299456799706857240000000000000)
      constant := (537513315904205282189035508147934989144084423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1393100811044765091/800000000000000000)
  centralHi := (21767200172574454547/12500000000000000000)
  directionLo := (180711129239717642707/100000000000000000000)
  directionHi := (45177782309929410677/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree015.table
  base := (223238951789687191416217173809255085391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-14836128318263673791788104282120000000000000)
      constant := (81047512207072022079506912173450987674316595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree015.table
  base := (916856961130252229047437439409361741737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-733857887130841556537416694356380000000000000)
      constant := (4017719961503311467464486203584068959494422417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180711129239717642707/100000000000000000000)
  centralHi := (45177782309929410677/25000000000000000000)
  directionLo := (93526894858645663061/50000000000000000000)
  directionHi := (187053789717291326123/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree016.table
  base := (-79827622061165864657512427903936880133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-15701997974208096056220052051920000000000000)
      constant := (87195037863830846835679691057537841303706403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree016.table
  base := (-63130954788725883648794155857566345567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-194186168393628254219308860178020000000000000)
      constant := (1083034195517375131872988045575528710629812553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93526894858645663061/50000000000000000000)
  centralHi := (187053789717291326123/100000000000000000000)
  directionLo := (96594161656007129163/50000000000000000000)
  directionHi := (193188323312014258327/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree017.table
  base := (-216340872557687826724644014043907868139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-16567867630152518320651999821720000000000000)
      constant := (94427045013693033151803864628293313991987745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree017.table
  base := (-1230735265323245227481789689496462588691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-819631460018184477217054187067780000000000000)
      constant := (4699858428916736079257001706276502392829982069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96594161656007129163/50000000000000000000)
  centralHi := (193188323312014258327/100000000000000000000)
  directionLo := (39826793132570471229/20000000000000000000)
  directionHi := (99566982831426178073/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree018.table
  base := (-1924887937393840020089654351419391254113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-17433737286096940585083947591520000000000000)
      constant := (102643947656741859645580841908222929967196583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree018.table
  base := (-1026525777593218035254493917493562537073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-431259123230927968778436466711740000000000000)
      constant := (2558014864468421492686103885696638558834735207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39826793132570471229/20000000000000000000)
  centralHi := (99566982831426178073/50000000000000000000)
  directionLo := (12806697511873543527/6250000000000000000)
  directionHi := (204907160189976696433/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree019.table
  base := (-2638208657203087047967606965891693092851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-18299606942041362849515895361320000000000000)
      constant := (111764761448463382983345209027790234102181541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree019.table
  base := (-274808670154241441863901294946027939571/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-452702516452763698948345839889590000000000000)
      constant := (2788356110397150106361106220865891341847539945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12806697511873543527/6250000000000000000)
  centralHi := (204907160189976696433/100000000000000000000)
  directionLo := (210522094597283256709/100000000000000000000)
  directionHi := (21052209459728325671/10000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree020.table
  base := (-16225557890147061374029487608460170929/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (6996)
      previous := (0)
      next := (4240)
      square := (86914946524724204573661423862500000000000)
      linear := (-2395684574748223139243480391390000000000000)
      constant := (15215453653384779289430291463495884496510975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree020.table
  base := (-834763005425438866130085320969438048851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-237072954837299714559127606533720000000000000)
      constant := (1519677768890790720303921699408345577518099509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210522094597283256709/100000000000000000000)
  centralHi := (21052209459728325671/10000000000000000000)
  directionLo := (107995555846217798967/50000000000000000000)
  directionHi := (43198222338487119587/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree021.table
  base := (-188233119381692767997581782473425100257/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-5007836563482551844594947725230000000000000)
      constant := (33116748868916413309691544749065744466890435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree021.table
  base := (-2402985127597067312804197507814961319/6250000000000000000000000000000000000)
  polynomial :=
    { denominator := 12289375000000000000000000000000000000000000
      center := (24751)
      previous := (0)
      next := (14575)
      square := (304202312836534716007814983518750000000000)
      linear := (-8849808980293484987288653325808750000000000)
      constant := (59102095479739840299279661561153129058450300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107995555846217798967/50000000000000000000)
  centralHi := (43198222338487119587/20000000000000000000)
  directionLo := (110662514369863405827/50000000000000000000)
  directionHi := (44265005747945362331/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree022.table
  base := (-263272838581097372916411236400317923471/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1755625000000000000000000000000000000000000
      center := (3498)
      previous := (0)
      next := (2120)
      square := (43457473262362102286830711931250000000000)
      linear := (-1306075994367164352675733666920000000000000)
      constant := (8996956782978557051326606715866506952969961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree022.table
  base := (-4280532788642879681321232675484025241699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1034065392236541778916147918846280000000000000)
      constant := (7196780810014070920344218280137963281707307941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110662514369863405827/50000000000000000000)
  centralHi := (44265005747945362331/20000000000000000000)
  directionLo := (9061335562765357263/4000000000000000000)
  directionHi := (28316673633641741447/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree023.table
  base := (-4600828865608185250304842352292877409597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-21763085565819051907243686440520000000000000)
      constant := (156141151953219261641397507259869307356442027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree023.table
  base := (-1164677854252918907446870861673769946907/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-269238044670053309813991666300495000000000000)
      constant := (1952261025429824566316242940773801880737773613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9061335562765357263/4000000000000000000)
  centralHi := (28316673633641741447/12500000000000000000)
  directionLo := (115812331359460938577/50000000000000000000)
  directionHi := (46324932543784375431/20000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree024.table
  base := (-247015288515161361769104348029493477553/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-5657238805440868542918908552580000000000000)
      constant := (42251931242337022555112696839445764107768115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree024.table
  base := (-4989362349383778032473234969209156203269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1119838965123884699595785411557680000000000000)
      constant := (8454841240993080592745155755201802531025851571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115812331359460938577/50000000000000000000)
  centralHi := (46324932543784375431/20000000000000000000)
  directionLo := (236606408189129627387/100000000000000000000)
  directionHi := (59151602047282406847/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree025.table
  base := (-261956696748888418782463999667207729563/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-5873706219426974109026895495030000000000000)
      constant := (45631901671436201581946961792299067438287665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree025.table
  base := (-5280638172407409436863311032436516866917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1162725751567556159935604157913380000000000000)
      constant := (9133050097656569903126411625259530381920677203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236606408189129627387/100000000000000000000)
  centralHi := (59151602047282406847/25000000000000000000)
  directionLo := (60371351035004455727/25000000000000000000)
  directionHi := (241485404140017822909/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree026.table
  base := (-688011710428718778870643549273682767201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (6996)
      previous := (0)
      next := (4240)
      square := (86914946524724204573661423862500000000000)
      linear := (-3045086816706539837567441218740000000000000)
      constant := (24585218896607624015220690338680225106932391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree026.table
  base := (-5539152109471941344980215113200668440943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1205612538011227620275422904269080000000000000)
      constant := (9842760421029229713498859972214926795120164537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60371351035004455727/25000000000000000000)
  centralHi := (241485404140017822909/100000000000000000000)
  directionLo := (49253551518311629897/20000000000000000000)
  directionHi := (123133878795779074743/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree027.table
  base := (-1148139757935498359665176482667566890071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-25226564189596740964971477519720000000000000)
      constant := (211454670239479189539821515565674023028952805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree027.table
  base := (-2885134339229543020479467371264391043357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-624249662227449540307620825312390000000000000)
      constant := (5291616916752651631680938488654940452401299163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49253551518311629897/20000000000000000000)
  centralHi := (123133878795779074743/50000000000000000000)
  directionLo := (125479496777044372289/50000000000000000000)
  directionHi := (250958993554088744579/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree028.table
  base := (-5953433065164913105207211624523248672017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-26092433845541163229403425289520000000000000)
      constant := (226833768859253427224776501365274194480304247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree028.table
  base := (-2989169734996997650292938993472075235859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (198008)
      previous := (0)
      next := (116600)
      square := (2433618502692277728062519868150000000000000)
      linear := (-92241865064183610068218599784320000000000000)
      constant := (810990812699968145510317546275718584637304483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125479496777044372289/50000000000000000000)
  centralHi := (250958993554088744579/100000000000000000000)
  directionLo := (255564129842565866949/100000000000000000000)
  directionHi := (5111282596851317339/2000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree029.table
  base := (-1536485688369319683501783457272376754903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-6739575875371396373458843264830000000000000)
      constant := (60702201183488174241168626071066893695477473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree029.table
  base := (-1233378881541012197738440925117387917671/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1334272897342242001294879143336180000000000000)
      constant := (12154187191693846550179340320704833048119229445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255564129842565866949/100000000000000000000)
  centralHi := (5111282596851317339/2000000000000000000)
  directionLo := (65021934990573842031/25000000000000000000)
  directionHi := (416140383939672589/160000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree030.table
  base := (-3160596493533353894010321603840888654443/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-13912086578715003879133660414560000000000000)
      constant := (129685724403259498099179942834610943769669613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree030.table
  base := (-6338796895783282479569228569105508987469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1377159683785913461634697889691880000000000000)
      constant := (12983787153371927457589730257868648637455779371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65021934990573842031/25000000000000000000)
  centralHi := (416140383939672589/160000000000000000)
  directionLo := (26453400631147838211/10000000000000000000)
  directionHi := (264534006311478382111/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree031.table
  base := (-324079750936660056888617554915201726129/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-7172510703343607505674817149730000000000000)
      constant := (69128731966959280620132253067920991756518195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree031.table
  base := (-3248184836110198621298751648547130926621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-710023235114792460987258318023790000000000000)
      constant := (6921175779426938011176303348933326852128958939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26453400631147838211/10000000000000000000)
  centralHi := (264534006311478382111/100000000000000000000)
  directionLo := (67226691365719833587/25000000000000000000)
  directionHi := (268906765462879334349/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree032.table
  base := (-6629109686802562981148258653509002959263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-29555912469318852287131216368720000000000000)
      constant := (294233733923049891819320106854133210687430233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree032.table
  base := (-6641496898785851488186547164774678148501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1462933256673256382314335382403280000000000000)
      constant := (14729621070229583898620993124767808524962173859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67226691365719833587/25000000000000000000)
  centralHi := (268906765462879334349/100000000000000000000)
  directionLo := (273209546919968928577/100000000000000000000)
  directionHi := (136604773459984464289/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree033.table
  base := (-1691332888328022242203048521906236910139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-7605445531315818637890791034630000000000000)
      constant := (78130846961848635183004618990630380519419549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree033.table
  base := (-6775706974520203117961856829450642084669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1505820043116927842654154128758980000000000000)
      constant := (15645385317126709656257254553164149172824074171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273209546919968928577/100000000000000000000)
  centralHi := (136604773459984464289/50000000000000000000)
  directionLo := (277445606461377241523/100000000000000000000)
  directionHi := (69361401615344310381/25000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree034.table
  base := (-3445778662662179683750515424371799553791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-15643825890603848407997555954160000000000000)
      constant := (165690123595366140624680121040579615053401081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree034.table
  base := (-6900239712395921867184781657286931703829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1548706829560599302993972875114680000000000000)
      constant := (16589473650447909588430283594947389433353272611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277445606461377241523/100000000000000000000)
  centralHi := (69361401615344310381/25000000000000000000)
  directionLo := (140808977484772009151/50000000000000000000)
  directionHi := (281617954969544018303/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree035.table
  base := (-7008841495171826902301817374048271448043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-32153521437152119080427059678120000000000000)
      constant := (350801349884101253666575886149998405502447213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree035.table
  base := (-3508050415802808285628907627164694270591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (198008)
      previous := (0)
      next := (116600)
      square := (2433618502692277728062519868150000000000000)
      linear := (-113685258286019340238127972962170000000000000)
      constant := (1254410545856985273030460401977698116557369167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140808977484772009151/50000000000000000000)
  centralHi := (281617954969544018303/100000000000000000000)
  directionLo := (285729383469279952733/100000000000000000000)
  directionHi := (142864691734639976367/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree036.table
  base := (-1779510396766268698126445298198489558691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-8254847773274135336214751861980000000000000)
      constant := (92696071785498482430169087509840442829636981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree036.table
  base := (-7124106160488392139011662968916823984391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1634480402447942223673610367826080000000000000)
      constant := (18562095000347939619489373536534599429964438369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (285729383469279952733/100000000000000000000)
  centralHi := (142864691734639976367/50000000000000000000)
  directionLo := (28978248496802138749/10000000000000000000)
  directionHi := (289782484968021387491/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree037.table
  base := (-7219854951552427758469118847116641162123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-33885260749040963609290955217720000000000000)
      constant := (391327100106720065272181077662389354975596493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree037.table
  base := (-288996699716126738783269327247673596399/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1677367188891613684013429114181780000000000000)
      constant := (19590424635529811385782170576636658962951131025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28978248496802138749/10000000000000000000)
  centralHi := (289782484968021387491/100000000000000000000)
  directionLo := (36722459197920574721/12500000000000000000)
  directionHi := (293779673583364597769/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree038.table
  base := (-1828712171666989662422411723404925010669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-8687782601246346468430725746880000000000000)
      constant := (103107048949975487421712675577895565645030779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree038.table
  base := (-7319071674033261763516792690915137003721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1720253975335285144353247860537480000000000000)
      constant := (20646662655635532296145103936908089627670837839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36722459197920574721/12500000000000000000)
  centralHi := (293779673583364597769/100000000000000000000)
  directionLo := (297723201358669661151/100000000000000000000)
  directionHi := (9303850042458426911/3125000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree039.table
  base := (-3701741984845772372278134854707675089473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-17808500030464904069077425378660000000000000)
      constant := (217043139387280203844845395795816140673670343) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree039.table
  base := (-1481400838808078692784901397995809807543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1763140761778956604693066606893180000000000000)
      constant := (21730749119363752849427391431379338711399869685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297723201358669661151/100000000000000000000)
  centralHi := (9303850042458426911/3125000000000000000)
  directionLo := (301615173099367913499/100000000000000000000)
  directionHi := (603230346198735827/200000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree040.table
  base := (-935766980452094150132957119705901865069/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (6996)
      previous := (0)
      next := (4240)
      square := (86914946524724204573661423862500000000000)
      linear := (-4560358714609278800323349815890000000000000)
      constant := (57037536941865813641736789802346121661021179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree040.table
  base := (-7489068326602673125834270129812221971403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-1806027548222628065032885353248880000000000000)
      constant := (22842635401772144368365232233417715955634119677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301615173099367913499/100000000000000000000)
  centralHi := (603230346198735827/200000000000000000)
  directionLo := (38182194938435551221/12500000000000000000)
  directionHi := (305457559507484409769/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree041.table
  base := (-7563109307391179069334664793769315948501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-37348739372818652667018746296920000000000000)
      constant := (479069389338956459523666179852321991500660691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree041.table
  base := (-756555065356272199304384909838898194879/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-924457167333149762686352049802290000000000000)
      constant := (11991141028724653311170528948515723567793297805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38182194938435551221/12500000000000000000)
  centralHi := (305457559507484409769/100000000000000000000)
  directionLo := (309252208847042980693/100000000000000000000)
  directionHi := (154626104423521490347/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree042.table
  base := (-763465240039227198592479547448559903411/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-19107304514381537465725347033360000000000000)
      constant := (251196431722019501414960985026604976156592505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree042.table
  base := (-7636683658074266343804226626906967773251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (396016)
      previous := (0)
      next := (233200)
      square := (4867237005384555456125039736300000000000000)
      linear := (-270257303015710140816074692280040000000000000)
      constant := (3592808155311639653241446415445108292674565587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309252208847042980693/100000000000000000000)
  centralHi := (154626104423521490347/50000000000000000000)
  directionLo := (62600171467267339523/20000000000000000000)
  directionHi := (19562553583521043601/6250000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree043.table
  base := (-770096684262527708586351414274824963211/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-19540239342353748597941320918260000000000000)
      constant := (263135075609339702734181960717440083391701505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree043.table
  base := (-3851327969894030315793452925065631034231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-967343953776821223026170796157990000000000000)
      constant := (13172367265962063862841081051849223978817410929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62600171467267339523/20000000000000000000)
  centralHi := (19562553583521043601/6250000000000000000)
  directionLo := (316705138432878142313/100000000000000000000)
  directionHi := (158352569216439071157/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree044.table
  base := (-7762216687245180509793276141665657905677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-39946348340651919460314589606320000000000000)
      constant := (550700791837565311369927376938541166942953307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree044.table
  base := (-1940905125274640667251964060981403908761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-494393673499328476598040084667920000000000000)
      constant := (6891873333068670378382723707288038584594227199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316705138432878142313/100000000000000000000)
  centralHi := (158352569216439071157/50000000000000000000)
  directionLo := (160183295575955123739/50000000000000000000)
  directionHi := (320366591151910247479/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree045.table
  base := (-7818535356711519505160558520612424489491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-40812217996596341724746537376120000000000000)
      constant := (575684410517007880406535182532499699609019781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree045.table
  base := (-7819701468688081513440181974678839513177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-2020461480440985366731979085027380000000000000)
      constant := (28817916403312459235270431653910954850566804543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160183295575955123739/50000000000000000000)
  centralHi := (320366591151910247479/100000000000000000000)
  directionLo := (161993333769326698451/50000000000000000000)
  directionHi := (323986667538653396903/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree046.table
  base := (-1967507841131029953917392932095522609519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-10419521913135190997294621286480000000000000)
      constant := (150305175610646525516030552766523676989861129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree046.table
  base := (-1967749886457268599421656488634801182643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-515837066721164206767949457845770000000000000)
      constant := (7523997471034584151230142560200962330419834837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161993333769326698451/50000000000000000000)
  centralHi := (323986667538653396903/100000000000000000000)
  directionLo := (32756673939719312753/10000000000000000000)
  directionHi := (327566739397193127531/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree047.table
  base := (-7916792968083304877973579802416840133153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-42543957308485186253610432915720000000000000)
      constant := (627309419699262467809129443858151096065973223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree047.table
  base := (-7917596435115294375034154445881952556707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-2106235053328328287411616577738780000000000000)
      constant := (31401702529125606858473839266511247168142291813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32756673939719312753/10000000000000000000)
  centralHi := (327566739397193127531/100000000000000000000)
  directionLo := (165554052182221853429/50000000000000000000)
  directionHi := (331108104364443706859/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree048.table
  base := (-159177839046995663088279992603722646863/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-21704913482214804259021190342760000000000000)
      constant := (326975180321541173785419920435883577124045825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree048.table
  base := (-3979779213018336494578388513190095090413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-1074560919885999873875717662047240000000000000)
      constant := (16367522607061293164163702189376322121660464267) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165554052182221853429/50000000000000000000)
  centralHi := (331108104364443706859/100000000000000000000)
  directionLo := (334611991405451659437/100000000000000000000)
  directionHi := (167305995702725829719/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree049.table
  base := (-7996386706679197424635109225245358607087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-44275696620374030782474328455320000000000000)
      constant := (681143361258345740781232625166865787672692617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree049.table
  base := (-7996939305102183307519692906041061805819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (396016)
      previous := (0)
      next := (233200)
      square := (4867237005384555456125039736300000000000000)
      linear := (-313144089459381601155893438635740000000000000)
      constant := (4870858647985770493214612584723349601712181003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334611991405451659437/100000000000000000000)
  centralHi := (167305995702725829719/50000000000000000000)
  directionLo := (338079565796024952071/100000000000000000000)
  directionHi := (42259945724503119009/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree050.table
  base := (-4014662363436876915621238257982302451011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-22570783138159226523453138112560000000000000)
      constant := (354444144064672125192864378216327712415110101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree050.table
  base := (-1003722839554502655744253558761422537781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (4258832379711486024109409769262500000000000)
      linear := (-279361926582417833553884102100735000000000000)
      constant := (4435574060904766222618447292831831540477285379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338079565796024952071/100000000000000000000)
  centralHi := (42259945724503119009/12500000000000000000)
  directionLo := (341511933649961160721/100000000000000000000)
  directionHi := (170755966824980580361/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree051.table
  base := (-1611548929965384798475089192164837594743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-46007435932262875311338223994920000000000000)
      constant := (737185032725044114608974816085264855981834565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree051.table
  base := (-2014531019154112979779657316652799026499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-569445549775753532192722890790395000000000000)
      constant := (9225196548340636581254129241860743339193651141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341511933649961160721/100000000000000000000)
  centralHi := (170755966824980580361/50000000000000000000)
  directionLo := (17245507302036825241/5000000000000000000)
  directionHi := (344910146040736504821/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree052.table
  base := (-505104869254907686184281640424137971377/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1755625000000000000000000000000000000000000
      center := (3498)
      previous := (0)
      next := (2120)
      square := (43457473262362102286830711931250000000000)
      linear := (-2929581599262956098485635735295000000000000)
      constant := (47877094171965062057298250337688596438402007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree052.table
  base := (-101024901599148673836198098133716190341/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 86025625000000000000000000000000000000000000
      center := (173257)
      previous := (0)
      next := (102025)
      square := (2129416189855743012054704884631250000000000)
      linear := (-145041811596667849319419394344830000000000000)
      constant := (2396536731134770178934719817462020849226372095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17245507302036825241/5000000000000000000)
  centralHi := (344910146040736504821/100000000000000000000)
  directionLo := (1393100811044765091/400000000000000000)
  directionHi := (348275202761191272751/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree053.table
  base := (-8101150075285801128954801654669960393629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530000000000000000000000000000000000000000
      center := (1056)
      previous := (0)
      next := (640)
      square := (13119237211279125218665875300000000000000)
      linear := (-900739155550032449815134330840000000000000)
      constant := (15008181856077956020937690228322492099137663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree053.table
  base := (-8101410198334019007295126495658641493051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25970000000000000000000000000000000000000000
      center := (52304)
      previous := (0)
      next := (30800)
      square := (642842623352677135714627889700000000000000)
      linear := (-44595391924346359423594887846660000000000000)
      constant := (751245165862959685600278510086079508042546553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1393100811044765091/400000000000000000)
  centralHi := (348275202761191272751/100000000000000000000)
  directionLo := (351608055759329272251/100000000000000000000)
  directionHi := (87902013939832318063/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree054.table
  base := (-162323639207032252233045928451248289109/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-24302522450048071052317033652160000000000000)
      constant := (412692684567454012913152962317351088897320475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree054.table
  base := (-8116397223474201655095885789740078899659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-2406442558434028509790347802228680000000000000)
      constant := (41315001864782176918016774603766005800172035581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351608055759329272251/100000000000000000000)
  centralHi := (87902013939832318063/25000000000000000000)
  directionLo := (354909612283694441081/100000000000000000000)
  directionHi := (177454806141847220541/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree055.table
  base := (-8126790497164044949034774657836134104039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-49470914556040564369066015074120000000000000)
      constant := (855888651472478425217316493446238299301754449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree055.table
  base := (-8126968575750844153870697416737212481393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-2449329344877699970130166548584380000000000000)
      constant := (42841609804419975115095525447874398336848586087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (354909612283694441081/100000000000000000000)
  centralHi := (177454806141847220541/50000000000000000000)
  directionLo := (358180737767776984047/100000000000000000000)
  directionHi := (22386296110486061503/6250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree056.table
  base := (-508311841758139971461845170821547335961/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1755625000000000000000000000000000000000000
      center := (3498)
      previous := (0)
      next := (2120)
      square := (43457473262362102286830711931250000000000)
      linear := (-3146049013249061664593622677745000000000000)
      constant := (55433965416878825442731518819682273533285551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree056.table
  base := (-2033284184202804761018922930149532400901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (99004)
      previous := (0)
      next := (58300)
      square := (1216809251346138864031259934075000000000000)
      linear := (-89007718975763265373928046247860000000000000)
      constant := (1585564853273708774582503261793429744401083637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358180737767776984047/100000000000000000000)
  centralHi := (22386296110486061503/6250000000000000000)
  directionLo := (180711129239717642707/50000000000000000000)
  directionHi := (72284451695887057083/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree057.table
  base := (-2033697523138523469647055526056531904747/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-12800663466982352224482477653430000000000000)
      constant := (229637430803157930848318448607892201879565677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree057.table
  base := (-8134911843069597183308817034061397664951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-2535102917765042890809804041295780000000000000)
      constant := (45977618731327591982549833044324440163998479409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180711129239717642707/50000000000000000000)
  centralHi := (72284451695887057083/20000000000000000000)
  directionLo := (364634963958316044193/100000000000000000000)
  directionHi := (182317481979158022097/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree058.table
  base := (-8132201505107013564511263311789741492301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-52068523523873831162361858383520000000000000)
      constant := (950707455440897995787870956367342616148126491) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree058.table
  base := (-813230212822107041645324399274857635487/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-1288994852104357175574811393825740000000000000)
      constant := (23793508595058593930596593050371016600969669165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (364634963958316044193/100000000000000000000)
  centralHi := (182317481979158022097/50000000000000000000)
  directionLo := (183909804630822463143/50000000000000000000)
  directionHi := (367819609261644926287/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree059.table
  base := (-1625046228984791434810445535339398356413/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-52934393179818253426793806153320000000000000)
      constant := (983416622458329925636237716991938150084179415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree059.table
  base := (-1625062856440449901613691831824771597117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-2620876490652385811489441534007180000000000000)
      constant := (49224010347223068281995418209524678063006095015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183909804630822463143/50000000000000000000)
  centralHi := (367819609261644926287/100000000000000000000)
  directionLo := (18548845851824302893/5000000000000000000)
  directionHi := (370976917036486057861/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree060.table
  base := (-4056942536010633565958099233700560378049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-26900131417881337845612876961560000000000000)
      constant := (508338603621170803533688748702135125898060359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree060.table
  base := (-4056976871188436348509494398454199303029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-1331881638548028635914630140181440000000000000)
      constant := (25444298727120525475010488555603765553731785411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18548845851824302893/5000000000000000000)
  centralHi := (370976917036486057861/100000000000000000000)
  directionLo := (93526894858645663061/25000000000000000000)
  directionHi := (74821515886916530449/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree061.table
  base := (-1619633644922719276528629717008951199483/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-54666132491707097955657701692920000000000000)
      constant := (1050489195921488079960077513725029280403261265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree061.table
  base := (-2024556232436208461137078298606754080401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-676662515884932183042269756679645000000000000)
      constant := (13145194475665072368578612233856319011619525959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93526894858645663061/25000000000000000000)
  centralHi := (74821515886916530449/20000000000000000000)
  directionLo := (377212259884152331729/100000000000000000000)
  directionHi := (37721225988415233173/10000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree062.table
  base := (-8078084628370763056986088614952601351609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-55532002147651520220089649462720000000000000)
      constant := (1084852577187662825185052559220038142803330319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree062.table
  base := (-4039065720278127888750039736382694376669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-1374768424991700096254448886537140000000000000)
      constant := (27150275598744660349433123624392279563300902171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377212259884152331729/100000000000000000000)
  centralHi := (37721225988415233173/10000000000000000000)
  directionLo := (95072898682871236247/25000000000000000000)
  directionHi := (380291594731484944989/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree063.table
  base := (-1006704695824092393272631806160865792439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (6996)
      previous := (0)
      next := (4240)
      square := (86914946524724204573661423862500000000000)
      linear := (-7049733975449492810565199654065000000000000)
      constant := (139970917727259527677365076133526627989038849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree063.table
  base := (-402683810087587478757025091711619527383/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (99004)
      previous := (0)
      next := (58300)
      square := (1216809251346138864031259934075000000000000)
      linear := (-99729415586681130458882732836785000000000000)
      constant := (2001711319137896856218396109366620876165340355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95072898682871236247/25000000000000000000)
  centralHi := (380291594731484944989/100000000000000000000)
  directionLo := (47918274345481100053/12500000000000000000)
  directionHi := (15333847790553952017/4000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree064.table
  base := (-8024829718603684031898774402233915913039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-57263741459540364748953545002320000000000000)
      constant := (1155233482286506704958568587435004930200273449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree064.table
  base := (-4012430798529865684259676426547687412417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1386056)
      previous := (0)
      next := (816200)
      square := (17035329518845944096437639077050000000000000)
      linear := (-1417655211435371556594267632892840000000000000)
      constant := (28911437394838450187683579314486509756867511703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47918274345481100053/12500000000000000000)
  centralHi := (15333847790553952017/4000000000000000000)
  directionLo := (386376646624028516653/100000000000000000000)
  directionHi := (193188323312014258327/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree065.table
  base := (-3995831636150992691557855826186453538649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14045000000000000000000000000000000000000000
      center := (27984)
      previous := (0)
      next := (16960)
      square := (347659786098896818294645695450000000000000)
      linear := (-29064805557742393506692746386060000000000000)
      constant := (595625496223573852420920804625892252009934959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree065.table
  base := (-1997922392322926374570355412969853441957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-719549302328603643382088503035345000000000000)
      constant := (14906356122881541908417940132323497652395596563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386376646624028516653/100000000000000000000)
  centralHi := (193188323312014258327/50000000000000000000)
  directionLo := (97345878531443267653/25000000000000000000)
  directionHi := (389383514125773070613/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree066.table
  base := (-1988535003923532825452727394911801247571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (13992)
      previous := (0)
      next := (8480)
      square := (173829893049448409147322847725000000000000)
      linear := (-14748870192857302319454360135480000000000000)
      constant := (306954966819372248997570135416072750295573061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree066.table
  base := (-7954161703330058216917586739766638213031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-2921083995758086033868172758497080000000000000)
      constant := (61455565823264117222849799754345960149720200129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97345878531443267653/25000000000000000000)
  centralHi := (389383514125773070613/100000000000000000000)
  directionLo := (392367339478508106243/100000000000000000000)
  directionHi := (98091834869627026561/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree067.table
  base := (-989032676417288341608587703344784964823/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3511250000000000000000000000000000000000000
      center := (6996)
      previous := (0)
      next := (4240)
      square := (86914946524724204573661423862500000000000)
      linear := (-7482668803421703942781173538965000000000000)
      constant := (158117512833650579611713161503996999033812193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree067.table
  base := (-989034911681767418150894168592889434223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 172051250000000000000000000000000000000000000
      center := (346514)
      previous := (0)
      next := (204050)
      square := (4258832379711486024109409769262500000000000)
      linear := (-370496347775219686775998938106597500000000000)
      constant := (7914162325843105644277423994086641730384112057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392367339478508106243/100000000000000000000)
  centralHi := (98091834869627026561/25000000000000000000)
  directionLo := (12354020138401460577/3125000000000000000)
  directionHi := (79065728885769347693/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree068.table
  base := (-7866028656890174564950444513323964498781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-60727220083318053806681336081520000000000000)
      constant := (1302611695258079870497866109329432983722924171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree068.table
  base := (-393302169898096323535365692397635913577/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-751714392161357238636952562802120000000000000)
      constant := (16299655674075789873662894402363544976096740715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12354020138401460577/3125000000000000000)
  centralHi := (79065728885769347693/20000000000000000000)
  directionLo := (398267931325704712291/100000000000000000000)
  directionHi := (99566982831426178073/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree069.table
  base := (-97693034179336117139161431680576751719/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1755625000000000000000000000000000000000000
      center := (3498)
      previous := (0)
      next := (2120)
      square := (43457473262362102286830711931250000000000)
      linear := (-3849568108703904754444580240707500000000000)
      constant := (83802165142855293100436895558982549522106645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree069.table
  base := (-1953863720871524887084500291906586438367/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 344102500000000000000000000000000000000000000
      center := (693028)
      previous := (0)
      next := (408100)
      square := (8517664759422972048218819538525000000000000)
      linear := (-762436088772275103721907249391045000000000000)
      constant := (16777884493163717885617805559044796786036727753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398267931325704712291/100000000000000000000)
  centralHi := (99566982831426178073/25000000000000000000)
  directionLo := (25074105257198591421/6250000000000000000)
  directionHi := (401185684115177462737/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree070.table
  base := (-7760504450100401677100067609491237525253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-62458959395206898335545231621120000000000000)
      constant := (1379608941486864105194431718697339113791564323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree070.table
  base := (-388025723047517542740454923578626713421/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 49157500000000000000000000000000000000000000
      center := (99004)
      previous := (0)
      next := (58300)
      square := (1216809251346138864031259934075000000000000)
      linear := (-110451112197598995543837419425710000000000000)
      constant := (2466144440640990477464989314439942314670014385) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25074105257198591421/6250000000000000000)
  centralHi := (401185684115177462737/100000000000000000000)
  directionLo := (404082369270758537799/100000000000000000000)
  directionHi := (2020411846353792689/500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 33
  qDenominator := 53
  table := BinomialMassData.Q33_53.Degree071.table
  base := (-7701214467516727273140630692989723187729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (55968)
      previous := (0)
      next := (33920)
      square := (695319572197793636589291390900000000000000)
      linear := (-63324829051151320599977179390920000000000000)
      constant := (1418934590998222978905269244575011867565669239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_53.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 467
  qDenominator := 742
  table := BinomialMassData.Q467_742.Degree071.table
  base := (-7701222714744300210189350743823722700883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (2772112)
      previous := (0)
      next := (1632400)
      square := (34070659037691888192875278154100000000000000)
      linear := (-3135517927976443335567266490275580000000000000)
      constant := (71020141711745773312642931185524563983727762997) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q467_742.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell548.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell548
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 71 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 71 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 71 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel071.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell548

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel072
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  degreePropagationTail 72 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel073
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  degreePropagationTail 73 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel074
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  degreePropagationTail 74 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel075
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  degreePropagationTail 75 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel076
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  degreePropagationTail 76 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel077
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  degreePropagationTail 77 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel078
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  degreePropagationTail 78 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel079
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  degreePropagationTail 79 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel080
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  degreePropagationTail 80 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel081
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  degreePropagationTail 81 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel082
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  degreePropagationTail 82 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel083
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  degreePropagationTail 83 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel084
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  degreePropagationTail 84 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel085
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  degreePropagationTail 85 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel086
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  degreePropagationTail 86 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel087
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  degreePropagationTail 87 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel088
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  degreePropagationTail 88 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel089
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  degreePropagationTail 89 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel090
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  degreePropagationTail 90 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel091
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  degreePropagationTail 91 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel092
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  degreePropagationTail 92 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel093
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  degreePropagationTail 93 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel094
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  degreePropagationTail 94 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel095
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  degreePropagationTail 95 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel096
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  degreePropagationTail 96 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel097
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  degreePropagationTail 97 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel098
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  degreePropagationTail 98 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel099
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  degreePropagationTail 99 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel100
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  degreePropagationTail 100 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel101
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  degreePropagationTail 101 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel102
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  degreePropagationTail 102 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel103
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  degreePropagationTail 103 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel104
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  degreePropagationTail 104 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel105
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  degreePropagationTail 105 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel106
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  degreePropagationTail 106 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel107
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  degreePropagationTail 107 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel108
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  degreePropagationTail 108 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel109
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  degreePropagationTail 109 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel110
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  degreePropagationTail 110 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel111
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  degreePropagationTail 111 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel112
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  degreePropagationTail 112 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel113
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  degreePropagationTail 113 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel114
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  degreePropagationTail 114 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell548.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 71 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell548.Kernel349

