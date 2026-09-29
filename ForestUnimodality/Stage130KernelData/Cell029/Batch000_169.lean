import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell029.Parameters
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch000_049
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch050_099
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch100_149
import ForestUnimodality.BinomialMassData.Q1613_3478.Batch150_199
import ForestUnimodality.BinomialMassData.Q22_47.Batch000_049
import ForestUnimodality.BinomialMassData.Q22_47.Batch050_099
import ForestUnimodality.BinomialMassData.Q22_47.Batch100_149
import ForestUnimodality.BinomialMassData.Q22_47.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree000.table
  base := (542425505946413625724034087/10000000000000000000000000)
  polynomial :=
    { denominator := 34780000000000000000000000000000000000000000
      center := (218205)
      previous := (188721)
      next := (0)
      square := (2947418359710085998814932398220000000000000)
      linear := (15257019764935812060624442778400000000000000)
      constant := (1886555909681626590268190554586000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree000.table
  base := (542425505946413625724034087/10000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (2925)
      previous := (2574)
      next := (0)
      square := (39829977833920081065066654030000000000000)
      linear := (206175942769402865684114091600000000000000)
      constant := (25493998779481440409029602089000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree001.table
  base := (166755220454619010350995121807890836027229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (21777771557011008457337420033308740000000000000)
      constant := (2005949499509595324883929617281624876749999162836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree001.table
  base := (331579429662904051744717643887633310927373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (7937750285469451120290429527880000000000000)
      constant := (728333253411483874902339111301741983838566957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24934291273026982011/50000000000000000000)
  directionHi := (49868582546053964023/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree002.table
  base := (214718114828626367109572268684953519799637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (17023585742798639741248934074979880000000000000)
      constant := (1278467266603457221022451792714869066499996088154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree002.table
  base := (212539772012816309285719355637163743861439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (6185231260776967553427496750560000000000000)
      constant := (462069271002680251695286420448734710189918751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24934291273026982011/50000000000000000000)
  centralHi := (49868582546053964023/100000000000000000000)
  directionLo := (70524825772951726743/100000000000000000000)
  directionHi := (8815603221618965843/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree003.table
  base := (72772106441094957894380979969194478241117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (12269399928586271025160448116651020000000000000)
      constant := (853294130127940155906959572996159843932019932628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree003.table
  base := (5746432415558790201067020596638477932387/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (4432712236084483986564563973240000000000000)
      constant := (307430594169954788508549796126199943816072075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/100000000000000000000)
  centralHi := (8815603221618965843/12500000000000000000)
  directionLo := (86374918671207987321/100000000000000000000)
  directionHi := (43187459335603993661/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree004.table
  base := (25979852104923274475049677025735463046853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (7515214114373902309071962158322160000000000000)
      constant := (596949461725370052189340867974065313957697129704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree004.table
  base := (102428669629768253896762062412351077271429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (2680193211392000419701631195920000000000000)
      constant := (214684072681341622970678891314643529692586661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86374918671207987321/100000000000000000000)
  centralHi := (43187459335603993661/50000000000000000000)
  directionLo := (24934291273026982011/25000000000000000000)
  directionHi := (19947433018421585609/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree005.table
  base := (77787311218669972719436539413761569522187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (2761028300161533592983476199993300000000000000)
      constant := (436513295683839063610491112393117727770011345254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree005.table
  base := (7663853754423944538138442967366551764829/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (927674186699516852838698418600000000000000)
      constant := (156869276406982810704934304302127128485072610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24934291273026982011/25000000000000000000)
  centralHi := (19947433018421585609/20000000000000000000)
  directionLo := (22301908102907240079/20000000000000000000)
  directionHi := (27877385128634050099/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree006.table
  base := (60539425927240876039200765213246739744383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-1993157514050835123105009758335560000000000000)
      constant := (332015852859303826166074828777488867685046524686) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree006.table
  base := (5965049193494011050702856838131847378579/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-824844837992966714024234358720000000000000)
      constant := (119318617212726280998823502352892508592810110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22301908102907240079/20000000000000000000)
  centralHi := (27877385128634050099/25000000000000000000)
  directionLo := (122152581433695409089/100000000000000000000)
  directionHi := (12215258143369540909/10000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree007.table
  base := (48521841474317910221192161318308541845997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-6747343328263203839193495716664420000000000000)
      constant := (261357394847345531668429840855605236751716587274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree007.table
  base := (23909722934926765719433587611091807475651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-2577363862685450280887167136040000000000000)
      constant := (93980098065747104155212972448243605427426118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122152581433695409089/100000000000000000000)
  centralHi := (12215258143369540909/10000000000000000000)
  directionLo := (131939867652155034383/100000000000000000000)
  directionHi := (8246241728259689649/6250000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree008.table
  base := (19846032924061701462367655043317510649809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-11501529142475572555281981674993280000000000000)
      constant := (212184435677665967604444779275694694495244171556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree008.table
  base := (39121250805354783275354617887967854664409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-4329882887377933847750099913360000000000000)
      constant := (76382374833177821066588412819160990953679481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131939867652155034383/100000000000000000000)
  centralHi := (8246241728259689649/6250000000000000000)
  directionLo := (70524825772951726743/50000000000000000000)
  directionHi := (141049651545903453487/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree009.table
  base := (32890078639445812596981108276745960087301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-16255714956687941271370467633322140000000000000)
      constant := (177480891190414701469432478150300444130337574842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree009.table
  base := (16206442752414185106055751559014275684181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-6082401912070417414613032690680000000000000)
      constant := (64000513603334801501075743752885069972711658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/50000000000000000000)
  centralHi := (141049651545903453487/100000000000000000000)
  directionLo := (149605747638161892067/100000000000000000000)
  directionHi := (37401436909540473017/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree010.table
  base := (27442200217675453737127230259124996018489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-21009900770900309987458953591651000000000000000)
      constant := (153172183949193747810649277909305184168857946338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree010.table
  base := (6758379996554538653313545134411199996093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-7834920936762900981475965468000000000000000)
      constant := (55374740945856037421007981571657363165477748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149605747638161892067/100000000000000000000)
  centralHi := (37401436909540473017/25000000000000000000)
  directionLo := (157698304529649210199/100000000000000000000)
  directionHi := (788491522648246051/500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree011.table
  base := (2294532119609505797119065184871739176981/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-25764086585112678703547439549979860000000000000)
      constant := (136820210830665481923299344389645080032619174020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree011.table
  base := (11294430196268075951530786848084611545989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-9587439961455384548338898245320000000000000)
      constant := (49634061730655070898617268395997813810179402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157698304529649210199/100000000000000000000)
  centralHi := (788491522648246051/500000000000000000)
  directionLo := (82697688566063590233/50000000000000000000)
  directionHi := (165395377132127180467/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree012.table
  base := (3829789648553527563706152088744751581451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-30518272399325047419635925508308720000000000000)
      constant := (126909927543888674773497937547387788972491795710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree012.table
  base := (3766824332438626679608065321028689475307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-11339958986147868115201831022640000000000000)
      constant := (46237745756681295772066780847401875254765815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82697688566063590233/50000000000000000000)
  centralHi := (165395377132127180467/100000000000000000000)
  directionLo := (86374918671207987321/50000000000000000000)
  directionHi := (172749837342415974643/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree013.table
  base := (15890369316217626812360598732524155677633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-35272458213537416135724411466637580000000000000)
      constant := (122457212285705063283032577118186509383998371186) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree013.table
  base := (1951268614581916796296711598958438343373/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-13092478010840351682064763799960000000000000)
      constant := (44834219897253625757609325967233522404087656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86374918671207987321/50000000000000000000)
  centralHi := (172749837342415974643/100000000000000000000)
  directionLo := (44950932851126526141/25000000000000000000)
  directionHi := (35960746280901220913/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree014.table
  base := (816170299131653608194406521994899776557/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-40026644027749784851812897424966440000000000000)
      constant := (122791559183796450962582325271114605829802604704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree014.table
  base := (12808242850043960580343667452088517255199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-14844997035532835248927696577280000000000000)
      constant := (45183367385685804379707831144223534616734591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44950932851126526141/25000000000000000000)
  centralHi := (35960746280901220913/20000000000000000000)
  directionLo := (186591150251388859511/100000000000000000000)
  directionHi := (23323893781423607439/12500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree015.table
  base := (10574857560351380520765029441219756869507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-44780829841962153567901383383295300000000000000)
      constant := (127434206989230081459948681606356489727940756694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree015.table
  base := (1293817464539927579303325110439669749007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-16597516060225318815790629354600000000000000)
      constant := (47113187206976374250068554184689843804451704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186591150251388859511/100000000000000000000)
  centralHi := (23323893781423607439/12500000000000000000)
  directionLo := (38628037939967373347/20000000000000000000)
  directionHi := (12071261856239804171/6250000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree016.table
  base := (8379817442974993307041792233347976034279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-49535015656174522283989869341624160000000000000)
      constant := (136028610650787201708218224860223109265519687518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree016.table
  base := (2044715902061576632541736412144246444659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-18350035084917802382653562131920000000000000)
      constant := (50495168782042319091267190799466561585006924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38628037939967373347/20000000000000000000)
  centralHi := (12071261856239804171/6250000000000000000)
  directionLo := (199474330184215856089/100000000000000000000)
  directionHi := (19947433018421585609/10000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree017.table
  base := (1607036431562558461318854463366228212939/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-54289201470386891000078355299953020000000000000)
      constant := (148299824903127269302591558768973676436330412952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree017.table
  base := (6248229051033952139304114908986686641887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-20102554109610285949516494909240000000000000)
      constant := (55229939197071057425976104662791590791928383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199474330184215856089/100000000000000000000)
  centralHi := (19947433018421585609/10000000000000000000)
  directionLo := (25701679154651722091/12500000000000000000)
  directionHi := (205613433237213776729/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree018.table
  base := (4683827833246293739774532848605220137513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-59043387284599259716166841258281880000000000000)
      constant := (164030024869445137810295499376698153854951902146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree018.table
  base := (4522925230900832389718333793587525439767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-21855073134302769516379427686560000000000000)
      constant := (61238613264419200369882713084274843696445303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25701679154651722091/12500000000000000000)
  centralHi := (205613433237213776729/100000000000000000000)
  directionLo := (211574477318855180229/100000000000000000000)
  directionHi := (21157447731885518023/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree019.table
  base := (3117757650063525964889677590115908279171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-63797573098811628432255327216610740000000000000)
      constant := (183043169729196178305621907680073126322229767382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree019.table
  base := (594811420502752164949270796564445798603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-23607592158995253083242360463880000000000000)
      constant := (68457361828945739040217900526014303845570135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211574477318855180229/100000000000000000000)
  centralHi := (21157447731885518023/10000000000000000000)
  directionLo := (54343027943966374067/25000000000000000000)
  directionHi := (217372111775865496269/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree020.table
  base := (341215311513423379302520436933318107013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-68551758913023997148343813174939600000000000000)
      constant := (205194956780067207365067054127762228870982605730) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree020.table
  base := (98620479804799274024799425593229180251/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-25360111183687736650105293241200000000000000)
      constant := (76833838241958621963460698258167092146791344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54343027943966374067/25000000000000000000)
  centralHi := (217372111775865496269/100000000000000000000)
  directionLo := (22301908102907240079/10000000000000000000)
  directionHi := (223019081029072400791/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree021.table
  base := (214516529880430929258856924067199075857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-73305944727236365864432299133268460000000000000)
      constant := (230365924194411148025891731167936593545918986788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree021.table
  base := (12596841983934302189520019196890392687/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-27112630208380220216968226018520000000000000)
      constant := (86324710970656898591336105140508271936139575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22301908102907240079/10000000000000000000)
  centralHi := (223019081029072400791/100000000000000000000)
  directionLo := (22852655431744591741/10000000000000000000)
  directionHi := (228526554317445917411/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree022.table
  base := (-364918228202837453899746285808320085397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-78060130541448734580520785091597320000000000000)
      constant := (258456496056304606613997485150231049020116555852) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree022.table
  base := (-831304836670468117330757367552772795423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-28865149233072703783831158795840000000000000)
      constant := (96893880410356768298944585714115924894910593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22852655431744591741/10000000000000000000)
  centralHi := (228526554317445917411/100000000000000000000)
  directionLo := (233904385494067120827/100000000000000000000)
  directionHi := (58476096373516780207/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree023.table
  base := (-446080076488718430145498886421838372677/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-82814316355661103296609271049926180000000000000)
      constant := (289383277299719991549218591680637774748653264664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree023.table
  base := (-468606271837746716987716471825394620581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-30617668257765187350694091573160000000000000)
      constant := (108511138253182583282649824590990813132546284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233904385494067120827/100000000000000000000)
  centralHi := (58476096373516780207/25000000000000000000)
  directionLo := (239161320197288080191/100000000000000000000)
  directionHi := (3736895628082626253/1562500000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree024.table
  base := (-2746004826205193932690207976840700295559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-87568502169873472012697757008255040000000000000)
      constant := (323076190952661629598291881303323929162987642722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree024.table
  base := (-565183765244489369915228062285250008723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-32370187282457670917557024350480000000000000)
      constant := (121151127114705984373681343923419413653654465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239161320197288080191/100000000000000000000)
  centralHi := (3736895628082626253/1562500000000000000)
  directionLo := (122152581433695409089/50000000000000000000)
  directionHi := (244305162867390818179/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree025.table
  base := (-3624649430774369308496726598703267486529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-92322687984085840728786242966583900000000000000)
      constant := (359476209719791371462720910804906377050740867982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree025.table
  base := (-1847721775179921652537533255080633818961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-34122706307150154484419957127800000000000000)
      constant := (134792513583888307080542658424053759787830302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122152581433695409089/50000000000000000000)
  centralHi := (244305162867390818179/100000000000000000000)
  directionLo := (249342912730269820111/100000000000000000000)
  directionHi := (15583932045641863757/6250000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree026.table
  base := (-2214244677073758700605351758757624288521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-97076873798298209444874728924912760000000000000)
      constant := (398533524910016480782248851632034717915894339836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree026.table
  base := (-898227579991789045868686730297923147569/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-35875225331842638051282889905120000000000000)
      constant := (149417319404537097693508969820819438835100395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249342912730269820111/100000000000000000000)
  centralHi := (15583932045641863757/6250000000000000000)
  directionLo := (254280875517541722929/100000000000000000000)
  directionHi := (25428087551754172293/10000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree027.table
  base := (-1291120818238229784471182987275324544279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-101831059612510578160963214883241620000000000000)
      constant := (440206048763089370466077273287843211110643569928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree027.table
  base := (-208794781762362114502163850819615903341/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-37627744356535121618145822682440000000000000)
      constant := (165010373895744541982038442445726711737993275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254280875517541722929/100000000000000000000)
  centralHi := (25428087551754172293/10000000000000000000)
  directionLo := (64781189003405990491/25000000000000000000)
  directionHi := (51824951202724792393/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree028.table
  base := (-5838517719430862267657751695687001578693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-106585245426722946877051700841570480000000000000)
      constant := (484458178107479978057778576225039378197682692294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree028.table
  base := (-1177487972324588223400885645319595456991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-39380263381227605185008755459760000000000000)
      constant := (181558861811381870164866177443285068177534405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64781189003405990491/25000000000000000000)
  centralHi := (51824951202724792393/20000000000000000000)
  directionLo := (131939867652155034383/50000000000000000000)
  directionHi := (263879735304310068767/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree029.table
  base := (-1613894228682782875388943449627925092801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-111339431240935315593140186799899340000000000000)
      constant := (531259767167492887377167377371535701323468376632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree029.table
  base := (-1624688486403829423315972583557154819183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-41132782405920088751871688237080000000000000)
      constant := (199051947801090042931434235874448980017699012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131939867652155034383/50000000000000000000)
  centralHi := (263879735304310068767/100000000000000000000)
  directionLo := (268550535708691789161/100000000000000000000)
  directionHi := (134275267854345894581/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree030.table
  base := (-7019884508489101940841360930767947764549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-116093617055147684309228672758228200000000000000)
      constant := (580585270288010138051033192139696706076648627142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree030.table
  base := (-441122649219584080046927083332121538421/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-42885301430612572318734621014400000000000000)
      constant := (217480463208296007900817480954709496346048176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268550535708691789161/100000000000000000000)
  centralHi := (134275267854345894581/50000000000000000000)
  directionLo := (273141475712821654627/100000000000000000000)
  directionHi := (68285368928205413657/25000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree031.table
  base := (-94187778144652615264436780662045207653/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-120847802869360053025317158716557060000000000000)
      constant := (632413024173001769435598878773265534533952317920) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree031.table
  base := (-7568579874563318732309742008419046824013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-44637820455305055885597553791720000000000000)
      constant := (236836644088872699743082445794962325565755283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273141475712821654627/100000000000000000000)
  centralHi := (68285368928205413657/25000000000000000000)
  directionLo := (5553130334495330027/2000000000000000000)
  directionHi := (277656516724766501351/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree032.table
  base := (-4002014794435109003893001410599396991847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-125601988683572421741405644674885920000000000000)
      constant := (686724645524228821512144635226510483878474634052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree032.table
  base := (-8033584606607330375293032989646375545551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-46390339479997539452460486569040000000000000)
      constant := (257113911599368936507107642059311156419877841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5553130334495330027/2000000000000000000)
  centralHi := (277656516724766501351/100000000000000000000)
  directionLo := (70524825772951726743/25000000000000000000)
  directionHi := (282099303091806906973/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree033.table
  base := (-4214743694022034802681984758413191605781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-130356174497784790457494130633214780000000000000)
      constant := (743504524629507947322475963770758707351735825996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree033.table
  base := (-528468860779906167517663367999699208341/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-48142858504690023019323419346360000000000000)
      constant := (278306687597652359491377635835058631180395696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/25000000000000000000)
  centralHi := (282099303091806906973/100000000000000000000)
  directionLo := (286473196529859903059/100000000000000000000)
  directionHi := (14323659826492995153/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree034.table
  base := (-4406794214825201081986450080383473187703/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-135110360311997159173582616591543640000000000000)
      constant := (802739399021379704628452163572738382720521663748) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree034.table
  base := (-8836473734532730426635994150502165457681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-49895377529382506586186352123680000000000000)
      constant := (300410239605278770620291688753700716503982671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286473196529859903059/100000000000000000000)
  centralHi := (14323659826492995153/5000000000000000000)
  directionLo := (5815626117803252801/2000000000000000000)
  directionHi := (290781305890162640051/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree035.table
  base := (-4579098410071786288580969604233480818091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-139864546126209527889671102549872500000000000000)
      constant := (864417994132894380983519770072950992019655307956) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree035.table
  base := (-14341123598237721728031140764857731273/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-51647896554074990153049284901000000000000000)
      constant := (323420550312532595005734656121274733835483520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5815626117803252801/2000000000000000000)
  centralHi := (290781305890162640051/100000000000000000000)
  directionLo := (295026513012544233821/100000000000000000000)
  directionHi := (147513256506272116911/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree036.table
  base := (-1892979623571223628772589526793826953713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-144618731940421896605759588508201360000000000000)
      constant := (928530720123551674329712546590030532389104887270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree036.table
  base := (-4741291252835425939269973470126276433107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-53400415578767473719912217678320000000000000)
      constant := (347334207635777204306103272693142110718533274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295026513012544233821/100000000000000000000)
  centralHi := (147513256506272116911/50000000000000000000)
  directionLo := (149605747638161892067/50000000000000000000)
  directionHi := (59842299055264756827/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree037.table
  base := (-973504166066972325720073601953987115027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1634660000000000000000000000000000000000000000
      center := (10255635)
      previous := (8869887)
      next := (0)
      square := (138528662906374041944301822716340000000000000)
      linear := (-4037105885260385549239137147744060000000000000)
      constant := (26893767996521713245669959527520780422549964180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree037.table
  base := (-975057655698158063883334273880971361091/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-55152934603459957286775150455640000000000000)
      constant := (372148312010570139391073907107609342633499810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149605747638161892067/50000000000000000000)
  centralHi := (59842299055264756827/20000000000000000000)
  directionLo := (303338745350220844891/100000000000000000000)
  directionHi := (75834686337555211223/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree038.table
  base := (-1993955267433426995250920480942194775899/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-154127103568846634037936560424859080000000000000)
      constant := (1064027132619970037025647746124452109921135402210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree038.table
  base := (-2495854318315452698377224608253351488183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-56905453628152440853638083232960000000000000)
      constant := (397860398156556821182471042250913386250415012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303338745350220844891/100000000000000000000)
  centralHi := (75834686337555211223/25000000000000000000)
  directionLo := (307410588555109347761/100000000000000000000)
  directionHi := (153705294277554673881/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree039.table
  base := (-10170080839399001545364844998212220018869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-158881289383059002754025046383187940000000000000)
      constant := (1135397951003185818298645023490016030968635721702) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree039.table
  base := (-10182053983513302749587450368894199323829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-58657972652844924420501016010280000000000000)
      constant := (424468369005972360941185650634672713693661739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307410588555109347761/100000000000000000000)
  centralHi := (153705294277554673881/50000000000000000000)
  directionLo := (155714599091536150967/50000000000000000000)
  directionHi := (62285839636614460387/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree040.table
  base := (-206735785332671562226467166612631420821/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-163635475197271371470113532341516800000000000000)
      constant := (1209176826186724303863237432855488245503537665900) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree040.table
  base := (-10347294606998456915440089910589204655449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-60410491677537407987363948787600000000000000)
      constant := (451970439865166116165125991435508446916113159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155714599091536150967/50000000000000000000)
  centralHi := (62285839636614460387/20000000000000000000)
  directionLo := (157698304529649210199/50000000000000000000)
  directionHi := (315396609059298420399/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree041.table
  base := (-2094122561826317263093976988770502463709/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-168389661011483740186202018299845660000000000000)
      constant := (1285359456719780606137965007109862298189458752110) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree041.table
  base := (-10479827030477143338524976089271464303963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-62163010702229891554226881564920000000000000)
      constant := (480365091192285533919456991353559335352545733) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157698304529649210199/50000000000000000000)
  centralHi := (315396609059298420399/100000000000000000000)
  directionLo := (319314729587058856193/100000000000000000000)
  directionHi := (159657364793529428097/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree042.table
  base := (-2643039531005246776043585214836402060377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-173143846825696108902290504258174520000000000000)
      constant := (1363942173393233792352633472635607019718165171064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree042.table
  base := (-10580237198644967490576223347729226336031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-63915529726922375121089814342240000000000000)
      constant := (509651028635498021717117991584706139023707521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319314729587058856193/100000000000000000000)
  centralHi := (159657364793529428097/50000000000000000000)
  directionLo := (323185352478123795539/100000000000000000000)
  directionHi := (16159267623906189777/5000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree043.table
  base := (-10641942917664929512712684557783528111713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-177898032639908477618378990216503380000000000000)
      constant := (1444921844993714597259827295759661783366556741454) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree043.table
  base := (-5324512216402326077537964900460770185989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-65668048751614858687952747119560000000000000)
      constant := (539827149194045864929397037393004317318300598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323185352478123795539/100000000000000000000)
  centralHi := (16159267623906189777/5000000000000000000)
  directionLo := (327010164339828612323/100000000000000000000)
  directionHi := (81752541084957153081/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree044.table
  base := (-10680409167218640938904254271334879501049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-182652218454120846334467476174832240000000000000)
      constant := (1528295798336429733992504846574018665736816394142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree044.table
  base := (-10686614410399004066500910826895706140309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-67420567776307342254815679896880000000000000)
      constant := (570892512546457903479834843608347385136057419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327010164339828612323/100000000000000000000)
  centralHi := (81752541084957153081/25000000000000000000)
  directionLo := (330790754264254360933/100000000000000000000)
  directionHi := (165395377132127180467/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree045.table
  base := (-10687934345657250199398722044856940083891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-187406404268333215050555962133161100000000000000)
      constant := (1614061750373477163486395279330745995993126930378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree045.table
  base := (-334167817785013909658740388057144359217/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-69173086800999825821678612674200000000000000)
      constant := (602846316742471577426170596314016579535668704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330790754264254360933/100000000000000000000)
  centralHi := (165395377132127180467/50000000000000000000)
  directionLo := (167264310771804300593/50000000000000000000)
  directionHi := (334528621543608601187/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree046.table
  base := (-10664840957205172391401225982880003804417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-192160590082545583766644448091489960000000000000)
      constant := (1702217750521261600925148395130223260029965315086) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree046.table
  base := (-1066960144162045185237907292576674882557/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-70925605825692309388541545451520000000000000)
      constant := (635687877582659775026231237950341251844315870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167264310771804300593/50000000000000000000)
  centralHi := (334528621543608601187/100000000000000000000)
  directionLo := (169112591309029611529/50000000000000000000)
  directionHi := (338225182618059223059/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree047.table
  base := (-10611404641973746354993227173980780479869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1286860000000000000000000000000000000000000000
      center := (8073585)
      previous := (6982677)
      next := (0)
      square := (109054479309273181956152498734140000000000000)
      linear := (-4189676082909743669845381575528060000000000000)
      constant := (38143875141312441745956430161599044283167577866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree047.table
  base := (-10615572578499700796201326003681956565067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (2925)
      previous := (2574)
      next := (0)
      square := (39829977833920081065066654030000000000000)
      linear := (-1546343081923080701178818685720000000000000)
      constant := (14242906619500970253020288213146948041441851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169112591309029611529/50000000000000000000)
  centralHi := (338225182618059223059/100000000000000000000)
  directionLo := (341881777347334072347/100000000000000000000)
  directionHi := (85470444336833518087/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree048.table
  base := (-5263930534098426243498135722495656714061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-201668961710970321198821420008147680000000000000)
      constant := (1885693468356236425651774006750771168488868538476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree048.table
  base := (-210630185534313279713634035988525068589/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-74430643875077276522267411006160000000000000)
      constant := (704032018779550002275633752940107406174344950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341881777347334072347/100000000000000000000)
  centralHi := (85470444336833518087/25000000000000000000)
  directionLo := (69099934936966389857/20000000000000000000)
  directionHi := (172749837342415974643/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree049.table
  base := (-10414411796481590070353028902419994557959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-206423147525182689914909905966476540000000000000)
      constant := (1981010541577587188319350021666742992274780941922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree049.table
  base := (-5208802148256212291679142835474129941993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-76183162899769760089130343783480000000000000)
      constant := (739533674764293796471225228161235293916274926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69099934936966389857/20000000000000000000)
  centralHi := (172749837342415974643/50000000000000000000)
  directionLo := (87270019455594437039/25000000000000000000)
  directionHi := (349080077822377748157/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree050.table
  base := (-10271229271912360138472711168468813292553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-211177333339395058630998391924805400000000000000)
      constant := (2078712308316134882187571265422780347753822658174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree050.table
  base := (-410960892855546531590757116548154997631/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-77935681924462243655993276560800000000000000)
      constant := (775921215284928398811239860378628140255828025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87270019455594437039/25000000000000000000)
  centralHi := (349080077822377748157/100000000000000000000)
  directionLo := (70524825772951726743/20000000000000000000)
  directionHi := (88156032216189658429/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree051.table
  base := (-2019692215157368299975764443676044636831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-215931519153607427347086877883134260000000000000)
      constant := (2178797875964476471784215923288654867168219994490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree051.table
  base := (-631306505724047368408885555077207917963/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-79688200949154727222856209338120000000000000)
      constant := (813194329446262814758388203951311163347515728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/20000000000000000000)
  centralHi := (88156032216189658429/25000000000000000000)
  directionLo := (178066456542762778913/50000000000000000000)
  directionHi := (356132913085525557827/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree052.table
  base := (-9896233548491548535481840782912151038511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-220685704967819796063175363841463120000000000000)
      constant := (2281266480385379944597057239564889765778534152338) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree052.table
  base := (-9898369921347977051112925848728809878509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-81440719973847210789719142115440000000000000)
      constant := (851352751474124827857232526618398058978373619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178066456542762778913/50000000000000000000)
  centralHi := (356132913085525557827/100000000000000000000)
  directionLo := (44950932851126526141/12500000000000000000)
  directionHi := (359607462809012209129/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree053.table
  base := (-2416163719483399552658967662393408322013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-225439890782032164779263849799791980000000000000)
      constant := (2386117467232201583697327978851513814054605795416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree053.table
  base := (-9666522693208217468322875907674839886261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-83193238998539694356582074892760000000000000)
      constant := (890396254101005896277941563684786278691249451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44950932851126526141/12500000000000000000)
  centralHi := (359607462809012209129/100000000000000000000)
  directionLo := (90762190239482327491/25000000000000000000)
  directionHi := (72609752191585861993/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree054.table
  base := (-4701908866762395099947461521870864174187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-230194076596244533495352335758120840000000000000)
      constant := (2493350276017912826997804239186730021450773741492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree054.table
  base := (-9405450408150210973635485282969002517683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-84945758023232177923445007670080000000000000)
      constant := (930324642932730747413648518259681473438438253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90762190239482327491/25000000000000000000)
  centralHi := (72609752191585861993/20000000000000000000)
  directionLo := (91614436075271556817/25000000000000000000)
  directionHi := (366457744301086227269/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree055.table
  base := (-2278450378384553210580463301957632930229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-234948262410456902211440821716449700000000000000)
      constant := (2602964426522543654136455818853449274163223570328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree055.table
  base := (-1139403544808888178941632024558854573479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-86698277047924661490307940447400000000000000)
      constant := (971137751648614981631711984734995921977479112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91614436075271556817/25000000000000000000)
  centralHi := (366457744301086227269/100000000000000000000)
  directionLo := (369835306431650591457/100000000000000000000)
  directionHi := (184917653215825295729/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree056.table
  base := (-4397337131684896704353191743426943506709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-239702448224669270927529307674778560000000000000)
      constant := (2714959507191072511165146945996220352702190688844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree056.table
  base := (-8795920979904912321337654243097746228647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-88450796072617145057170873224720000000000000)
      constant := (1012835437910122167574309520211557078580918777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369835306431650591457/100000000000000000000)
  centralHi := (184917653215825295729/50000000000000000000)
  directionLo := (373182300502777719023/100000000000000000000)
  directionHi := (23323893781423607439/6250000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree057.table
  base := (-8446494313538806324655818200022841274783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-244456634038881639643617793633107420000000000000)
      constant := (2829335165226402840693393647124809595442523918514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree057.table
  base := (-4223791715488206741532918179150764876373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-90203315097309628624033806002040000000000000)
      constant := (1055417579872071062156844550418951920776184086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373182300502777719023/100000000000000000000)
  centralHi := (23323893781423607439/6250000000000000000)
  directionLo := (37649954174434009457/10000000000000000000)
  directionHi := (376499541744340094571/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree058.table
  base := (-2017327919725469781584715836561012858751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-249210819853094008359706279591436280000000000000)
      constant := (2946091098126578164078583835530977805860648537032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree058.table
  base := (-8070262940264612063262059754998742695463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-91955834122002112190896738779360000000000000)
      constant := (1098884073206530647428600369373847777385722233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37649954174434009457/10000000000000000000)
  centralHi := (376499541744340094571/100000000000000000000)
  directionLo := (1483546131960125331/390625000000000000)
  directionHi := (379787809781792084737/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree059.table
  base := (-7663169254324325651115257459694286942323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-253965005667306377075794765549765140000000000000)
      constant := (3065227046453072505826417171503298611555390453834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree059.table
  base := (-3831999978049213148384774538691373016259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-93708353146694595757759671556680000000000000)
      constant := (1143234828563142343008808293837221514014167738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1483546131960125331/390625000000000000)
  centralHi := (379787809781792084737/100000000000000000000)
  directionLo := (47880981346982136987/12500000000000000000)
  directionHi := (383047850775857095897/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree060.table
  base := (-3614051918387097508862110912407714223883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-258719191481518745791883251508094000000000000000)
      constant := (3186742787648918238598872109821916683414226872628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree060.table
  base := (-3614414563998938743640155268838682775203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-95460872171387079324622604334000000000000000)
      constant := (1188469769401116421837612682086270699499153146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47880981346982136987/12500000000000000000)
  centralHi := (383047850775857095897/100000000000000000000)
  directionLo := (386280379399673733471/100000000000000000000)
  directionHi := (12071261856239804171/3125000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree061.table
  base := (-1691036749832480951785028455593797817661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-263473377295731114507971737466422860000000000000)
      constant := (3310638130752496292972563141253462733398857592152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree061.table
  base := (-6764780144763807366423164124770968877193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-97213391196079562891485537111320000000000000)
      constant := (1234588830137891824529845470765540929750280663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386280379399673733471/100000000000000000000)
  centralHi := (12071261856239804171/3125000000000000000)
  directionLo := (97371520167060553633/25000000000000000000)
  directionHi := (389486080668242214533/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree062.table
  base := (-6271325838797164053386592361323628637283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-268227563109943483224060223424751720000000000000)
      constant := (3436912911875768658477922942991150873683582193514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree062.table
  base := (-6271878450383269160400416566101547237383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-98965910220772046458348469888640000000000000)
      constant := (1281591954567701150508825764314121682152620953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97371520167060553633/25000000000000000000)
  centralHi := (389486080668242214533/100000000000000000000)
  directionLo := (392665611633436879151/100000000000000000000)
  directionHi := (24541600727089804947/6250000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree063.table
  base := (-5749663615409228141951176207528436850951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-272981748924155851940148709383080580000000000000)
      constant := (3565566990335215285345925713559471937043730421858) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree063.table
  base := (-5750145855751178325297172119465281289979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-100718429245464530025211402665960000000000000)
      constant := (1329479094510277531532061567426541193630436389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392665611633436879151/100000000000000000000)
  centralHi := (24541600727089804947/6250000000000000000)
  directionLo := (395819602956465103149/100000000000000000000)
  directionHi := (7916392059129302063/2000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree064.table
  base := (-2599590150175099408668957381187483789751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-277735934738368220656237195341409440000000000000)
      constant := (3696600245340281814589786792198892181337017664516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree064.table
  base := (-1299900265380815600753155507636190640543/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-102470948270157013592074335443280000000000000)
      constant := (1378250208655872465459497566641086619500162052) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395819602956465103149/100000000000000000000)
  centralHi := (7916392059129302063/2000000000000000000)
  directionLo := (398948660368431712179/100000000000000000000)
  directionHi := (19947433018421585609/5000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree065.table
  base := (-1154973261128886618499460678210241495099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-282490120552580589372325681299738300000000000000)
      constant := (3830012573158201924560030863972175955236797736168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree065.table
  base := (-2310130052568232029379211700966034622973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-104223467294849497158937268220600000000000000)
      constant := (1427905261577787745943681211418132059035705286) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398948660368431712179/100000000000000000000)
  centralHi := (19947433018421585609/5000000000000000000)
  directionLo := (50256670753573673281/12500000000000000000)
  directionHi := (402053366028589386249/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree066.table
  base := (-4011816579949190459643899119964407894837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-287244306366792958088414167258067160000000000000)
      constant := (3965803884686008836413207926906912809665315273446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree066.table
  base := (-4012136743098091014250674359981349415339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-105975986319541980725800200997920000000000000)
      constant := (1478444222887898730227341640996561199141516149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50256670753573673281/12500000000000000000)
  centralHi := (402053366028589386249/100000000000000000000)
  directionLo := (81026855957780188821/20000000000000000000)
  directionHi := (202567139894450472053/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree067.table
  base := (-3374963563715252531353317794779088909463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-291998492181005326804502653216396020000000000000)
      constant := (4103974103370715732245049658223388078736051685954) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree067.table
  base := (-210952673625085394951901508056509917031/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-107728505344234464292663133775240000000000000)
      constant := (1529867066514276988593600877640090713492456336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81026855957780188821/20000000000000000000)
  centralHi := (202567139894450472053/50000000000000000000)
  directionLo := (40819194037269289287/10000000000000000000)
  directionHi := (408191940372692892871/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree068.table
  base := (-1354672436266219252794481473785082530123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-296752677995217695520591139174724880000000000000)
      constant := (4244523163427295713350781071164658249735687612468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree068.table
  base := (-1354794169164031974496304371076636711853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-109481024368926947859526066552560000000000000)
      constant := (1582173770083106282331032407650823419007033446) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40819194037269289287/10000000000000000000)
  centralHi := (408191940372692892871/100000000000000000000)
  directionLo := (25701679154651722091/6250000000000000000)
  directionHi := (411226866474427553457/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree069.table
  base := (-402993971056229100104176511570334411903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-301506863809430064236679625133053740000000000000)
      constant := (4387451008311457708903607118399011392279414877370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree069.table
  base := (-1007591058955504758885552459978597451389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-111233543393619431426388999329880000000000000)
      constant := (1635364314389709899657793597353774556459763398) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25701679154651722091/6250000000000000000)
  centralHi := (411226866474427553457/100000000000000000000)
  directionLo := (414239557786951663057/100000000000000000000)
  directionHi := (207119778893475831529/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree070.table
  base := (-161480818681995811062985920016515164343/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-306261049623642432952768111091382600000000000000)
      constant := (4532757589410489346915226594739942278315070119952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree070.table
  base := (-1292031580918612529166001461981760802711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-112986062418311914993251932107200000000000000)
      constant := (1689438682945739823980431850590482290386811401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414239557786951663057/100000000000000000000)
  centralHi := (207119778893475831529/50000000000000000000)
  directionLo := (83446099192396492573/20000000000000000000)
  directionHi := (208615247980991231433/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree071.table
  base := (-67497733344014346025171944310973745987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-311015235437854801668856597049711460000000000000)
      constant := (4680442864920785347113704991331025165228992761168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree071.table
  base := (-270071568681708492899669715488473636643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-114738581443004398560114864884520000000000000)
      constant := (1744396861591478345597155078653331923473311226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83446099192396492573/20000000000000000000)
  centralHi := (208615247980991231433/50000000000000000000)
  directionLo := (210100072754529562961/50000000000000000000)
  directionHi := (420200145509059125923/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree072.table
  base := (481236495559129853310959615422490959/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-315769421252067170384945083008040320000000000000)
      constant := (4830506798885239498245010610613695398781422039000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree072.table
  base := (240477706595807896359270866768689021333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-116491100467696882126977797661840000000000000)
      constant := (1800238838163820743309886412375732034048124597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210100072754529562961/50000000000000000000)
  centralHi := (420200145509059125923/100000000000000000000)
  directionLo := (211574477318855180229/50000000000000000000)
  directionHi := (423148954637710360459/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree073.table
  base := (65621792451085800387174355480380209851/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-320523607066279539101033568966369180000000000000)
      constant := (4982949360367567548928649118684270797179034111072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree073.table
  base := (1049826219912896064039456648013219074101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-118243619492389365693840730439160000000000000)
      constant := (1856964602211886036306951598279501200934689109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211574477318855180229/50000000000000000000)
  centralHi := (423148954637710360459/100000000000000000000)
  directionLo := (85215471209432306567/20000000000000000000)
  directionHi := (106519339011790383209/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree074.table
  base := (188800502565043549618603809894621173667/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1634660000000000000000000000000000000000000000
      center := (10255635)
      previous := (8869887)
      next := (0)
      square := (138528662906374041944301822716340000000000000)
      linear := (-8791291699472754265327623106072920000000000000)
      constant := (138858662776863439853132913272205081447746498220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree074.table
  base := (235987292045034428191088825391236386199/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-119996138517081849260703663216480000000000000)
      constant := (1914574144753377517837757707717673929416908728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85215471209432306567/20000000000000000000)
  centralHi := (106519339011790383209/25000000000000000000)
  directionLo := (428985767667520942539/100000000000000000000)
  directionHi := (21449288383376047127/5000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree075.table
  base := (1377391748841435947615879046780487069057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-330031978694704276533210540883026900000000000000)
      constant := (5294970263095195352452338209487561038343054895588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree075.table
  base := (550938112004350943962137007174012782321/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-121748657541774332827566595993800000000000000)
      constant := (1973067458065816321406719628629236971180735445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428985767667520942539/100000000000000000000)
  centralHi := (21449288383376047127/5000000000000000000)
  directionLo := (215937296678019968303/50000000000000000000)
  directionHi := (431874593356039936607/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree076.table
  base := (3650280832186102009373630885070601495227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-334786164508916645249299026841355760000000000000)
      constant := (5454548561685120453668091923998534864928694740934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree076.table
  base := (3650199884298441008034456704070182044271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-123501176566466816394429528771120000000000000)
      constant := (2032444535507625492511915671572251032135794639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215937296678019968303/50000000000000000000)
  centralHi := (431874593356039936607/100000000000000000000)
  directionLo := (54343027943966374067/12500000000000000000)
  directionHi := (434744223551730992537/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree077.table
  base := (4574494218266762755614261658628116023899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-339540350323129013965387512799684620000000000000)
      constant := (5616505401512759282093344605394769778716618935558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree077.table
  base := (4574423722484064374763943962814600468409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-125253695591159299961292461548440000000000000)
      constant := (2092705371364770880910147532193097452434715481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54343027943966374067/12500000000000000000)
  centralHi := (434744223551730992537/100000000000000000000)
  directionLo := (218797517945673946507/50000000000000000000)
  directionHi := (87519007178269578603/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree078.table
  base := (2763710616854909035673929268807783100889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-344294536137341382681475998758013480000000000000)
      constant := (5780840767927969123582729273804846267355374174276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree078.table
  base := (2763679924123799873967949739946681586731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-127006214615851783528155394325760000000000000)
      constant := (2153849960719287252217227497134924439250177558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218797517945673946507/50000000000000000000)
  centralHi := (87519007178269578603/20000000000000000000)
  directionLo := (110106848947369825029/25000000000000000000)
  directionHi := (440427395789479300117/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree079.table
  base := (6509059790406198620963436707842856807533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-349048721951553751397564484716342340000000000000)
      constant := (5947554648301361004399691475214217600943307006986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree079.table
  base := (6509006344601520637928615549910303961659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-128758733640544267095018327103080000000000000)
      constant := (2215878299336549160417581214076511861451304731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110106848947369825029/25000000000000000000)
  centralHi := (440427395789479300117/100000000000000000000)
  directionLo := (17729666279411138281/4000000000000000000)
  directionHi := (221620828492639228513/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree080.table
  base := (234981502733996746769520738430723547203/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-353802907765766120113652970674671200000000000000)
      constant := (6116647031740849399030778174031350919954629348032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree080.table
  base := (3759680780069690451834360515530720577657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-130511252665236750661881259880400000000000000)
      constant := (2278790383568599765985577606165614723512088626) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17729666279411138281/4000000000000000000)
  centralHi := (221620828492639228513/50000000000000000000)
  directionLo := (446038162058144801581/100000000000000000000)
  directionHi := (223019081029072400791/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree081.table
  base := (855846457107615896892890944501574922569/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-358557093579978488829741456633000060000000000000)
      constant := (6288117908848199583197237349436092050128285736980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree081.table
  base := (1069803008937733987409393094033500548099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-132263771689929234228744192657720000000000000)
      constant := (2342586210271238356122465387185320021686005528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446038162058144801581/100000000000000000000)
  centralHi := (223019081029072400791/50000000000000000000)
  directionLo := (448817242914485676201/100000000000000000000)
  directionHi := (224408621457242838101/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree082.table
  base := (1925245579940961419283352045251823038081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-363311279394190857545829942591328920000000000000)
      constant := (6461967271509899460958983032818071903377445518010) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree082.table
  base := (2406548162795111088219014780785159792337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-134016290714621717795607125435040000000000000)
      constant := (2407265776732898545486679689988457671925089732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448817242914485676201/100000000000000000000)
  centralHi := (224408621457242838101/50000000000000000000)
  directionLo := (451579221247516038739/100000000000000000000)
  directionHi := (22578961062375801937/5000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree083.table
  base := (1072269691461451873030043879162153248041/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-368065465208403226261918428549657780000000000000)
      constant := (6638195112717492235833131941139131345852379939220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree083.table
  base := (10722666239895762345612447993217820774273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-135768809739314201362470058212360000000000000)
      constant := (2472829080613632281033460947898658166090369057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451579221247516038739/100000000000000000000)
  centralHi := (22578961062375801937/5000000000000000000)
  directionLo := (454324408971899328481/100000000000000000000)
  directionHi := (227162204485949664241/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree084.table
  base := (5923935307114280726727460330791373182247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-372819651022615594978006914507986640000000000000)
      constant := (6816801426413199448591666982091207833037079919548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree084.table
  base := (3702451225905581124194116061444339553/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-137521328764006684929332990989680000000000000)
      constant := (2539276119892756887250149684731297747432246400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454324408971899328481/100000000000000000000)
  centralHi := (227162204485949664241/50000000000000000000)
  directionLo := (457053108634891834821/100000000000000000000)
  directionHi := (228526554317445917411/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree085.table
  base := (104013985057748644741361974593953516847/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-377573836836827963694095400466315500000000000000)
      constant := (6997786207357257558709183406760257950830216621750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree085.table
  base := (13001724909628612125650433421558687639977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-139273847788699168496195923767000000000000000)
      constant := (2606606892823929468259068083317223140996709193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457053108634891834821/100000000000000000000)
  centralHi := (228526554317445917411/50000000000000000000)
  directionLo := (459765613805524646221/100000000000000000000)
  directionHi := (229882806902762323111/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree086.table
  base := (1418432871865314927686681670395000867849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-382328022651040332410183886424644360000000000000)
      constant := (7181149451013899813064088989601375788389607714580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree086.table
  base := (14184308516267340827267288243172043668271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-141026366813391652063058856544320000000000000)
      constant := (2674821397896590143921616366329327044463210639) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459765613805524646221/100000000000000000000)
  centralHi := (229882806902762323111/50000000000000000000)
  directionLo := (231231104721620136763/50000000000000000000)
  directionHi := (462462209443240273527/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree087.table
  base := (15395611723793833321330872135311712907791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-387082208465252701126272372382973220000000000000)
      constant := (7366891153453350925006162220500815730100843653422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree087.table
  base := (1924449268843623228131643826553544850829/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-142778885838084135629921789321640000000000000)
      constant := (2743919633802867196969018678952494244603850088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231231104721620136763/50000000000000000000)
  centralHi := (462462209443240273527/100000000000000000000)
  directionLo := (23257158612364711613/5000000000000000000)
  directionHi := (465143172247294232261/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree088.table
  base := (16635596584165277111260205750752035243643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-391836394279465069842360858341302080000000000000)
      constant := (7555011311267575582741020567165287511146081825606) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree088.table
  base := (519861915621969821291367253843735086447/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-144531404862776619196784722098960000000000000)
      constant := (2813901599409166964542830472277145945790765536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23257158612364711613/5000000000000000000)
  centralHi := (465143172247294232261/100000000000000000000)
  directionLo := (93561754197626848331/20000000000000000000)
  directionHi := (58476096373516780207/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree089.table
  base := (8952141405289377544607598970209841076429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-396590580093677438558449344299630940000000000000)
      constant := (7745509921497841990425684309806464924223566175636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree089.table
  base := (17904269518411670452165554545715439762881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-146283923887469102763647654876280000000000000)
      constant := (2884767293731782391664746740355045406436204129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93561754197626848331/20000000000000000000)
  centralHi := (58476096373516780207/12500000000000000000)
  directionLo := (235229633410940184739/50000000000000000000)
  directionHi := (470459266821880369479/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree090.table
  base := (4800417494458506293950099207981429741119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-401344765907889807274537830257959800000000000000)
      constant := (7938386981572436185505386541800786574321140251192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree090.table
  base := (4800414604832169064922737756046638907727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-148036442912161586330510587653600000000000000)
      constant := (2956516715915949282600713759640428101388675772) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235229633410940184739/50000000000000000000)
  centralHi := (470459266821880369479/100000000000000000000)
  directionLo := (473094913588947630597/100000000000000000000)
  directionHi := (236547456794473815299/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree091.table
  base := (5131939428965812274274721091846098807579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-406098951722102175990626316216288660000000000000)
      constant := (8133642489253098325682615454839989434376596904472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree091.table
  base := (20527747665937488617903249286483224379491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-149788961936854069897373520430920000000000000)
      constant := (3029149865217860749493764836904601442654295619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473094913588947630597/100000000000000000000)
  centralHi := (236547456794473815299/50000000000000000000)
  directionLo := (475715958097777526643/100000000000000000000)
  directionHi := (118928989524444381661/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree092.table
  base := (10941272851057068388678143734489958388949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-410853137536314544706714802174617520000000000000)
      constant := (8331276442588954102925010267991158749812587355316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree092.table
  base := (21882536964758409472992001437886949851901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-151541480961546553464236453208240000000000000)
      constant := (3102666740989220139343032692748132272222849309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475715958097777526643/100000000000000000000)
  centralHi := (118928989524444381661/25000000000000000000)
  directionLo := (478322640394576160383/100000000000000000000)
  directionHi := (3736895628082626253/781250000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree093.table
  base := (23266033654998120298716131570003412550331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-415607323350526913422803288132946380000000000000)
      constant := (8531288839876887714031938901807994124930239068102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree093.table
  base := (23266026059542029152124446381685000708003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-153293999986239037031099385985560000000000000)
      constant := (3177067342663972506181229757908382166563978627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478322640394576160383/100000000000000000000)
  centralHi := (3736895628082626253/781250000000000000)
  directionLo := (120228798504973325829/25000000000000000000)
  directionHi := (480915194019893303317/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree094.table
  base := (3084777666031743203966213457572684666849/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1286860000000000000000000000000000000000000000
      center := (8073585)
      previous := (6982677)
      next := (0)
      square := (109054479309273181956152498734140000000000000)
      linear := (-8943861897122112385933867533856920000000000000)
      constant := (185822971906967053178932349736408527992305043312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree094.table
  base := (6169553681527278822210671830667574125051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (2925)
      previous := (2574)
      next := (0)
      square := (39829977833920081065066654030000000000000)
      linear := (-3298862106615564268041751463040000000000000)
      constant := (69198971696742679270443628475845503935509588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120228798504973325829/25000000000000000000)
  centralHi := (480915194019893303317/100000000000000000000)
  directionLo := (241746923126409314031/50000000000000000000)
  directionHi := (483493846252818628063/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree095.table
  base := (26119108506098167870410832706543658432417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-425115694978951650854980260049604100000000000000)
      constant := (8938448960535534964673583191753821654764598660914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree095.table
  base := (13059551383958547870155452386939539853523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-156799038035624004164825251540200000000000000)
      constant := (3328519721803857856068370708870498887072864614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241746923126409314031/50000000000000000000)
  centralHi := (483493846252818628063/100000000000000000000)
  directionLo := (486058818343517779417/100000000000000000000)
  directionHi := (243029409171758889709/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree096.table
  base := (6897173749763036256292475471408934823147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-429869880793164019571068746007932960000000000000)
      constant := (9145596681455125429238827753586496155090481030296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree096.table
  base := (1724293125765643821673230341952265679329/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-158551557060316487731688184317520000000000000)
      constant := (3405571498453299383638086143525320878170204176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486058818343517779417/100000000000000000000)
  centralHi := (243029409171758889709/50000000000000000000)
  directionLo := (488610325734781636357/100000000000000000000)
  directionHi := (244305162867390818179/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree097.table
  base := (29086980640350672117155387949431861011977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-434624066607376388287157231966261820000000000000)
      constant := (9355122841377586576213855204241150602910801794434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree097.table
  base := (29086976306945738728207489081395469028601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-160304076085008971298551117094840000000000000)
      constant := (3483506999359102457368938095732842591084179609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488610325734781636357/100000000000000000000)
  centralHi := (244305162867390818179/50000000000000000000)
  directionLo := (767419653551900999/156250000000000000)
  directionHi := (491148578273216639361/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree098.table
  base := (30613965282850745925235838788932660349629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-439378252421588757003245717924590680000000000000)
      constant := (9567027439412961913510483007551146471498360802218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree098.table
  base := (478343148712167066723024173589456620199/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-162056595109701454865414049872160000000000000)
      constant := (3562326224224322879143438971888423019137253824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (767419653551900999/156250000000000000)
  centralHi := (491148578273216639361/100000000000000000000)
  directionLo := (493673780410662087201/100000000000000000000)
  directionHi := (246836890205331043601/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree099.table
  base := (2010603049773150850276724636404504611081/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-444132438235801125719334203882919540000000000000)
      constant := (9781310474773879486289661500450073765446940313632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree099.table
  base := (32169645525043182393065780956271643396911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-163809114134393938432276982649480000000000000)
      constant := (3642029172785855540511380662364764060263776399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493673780410662087201/100000000000000000000)
  centralHi := (246836890205331043601/50000000000000000000)
  directionLo := (2480930656981907707/500000000000000000)
  directionHi := (496186131396381541401/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree100.table
  base := (4219253883174687899796589684076687210787/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-448886624050013494435422689841248400000000000000)
      constant := (9997971946761693724613724443413084806473158291632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree100.table
  base := (675080564469430629725415809205230036679/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-165561633159086421999139915426800000000000000)
      constant := (3722615844809838741631580866206717657551195550) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2480930656981907707/500000000000000000)
  centralHi := (496186131396381541401/100000000000000000000)
  directionLo := (498685825460539640223/100000000000000000000)
  directionHi := (15583932045641863757/3125000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree101.table
  base := (35367111987116490257488087963359163200153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-453640809864225863151511175799577260000000000000)
      constant := (10217011854754551455254676323355576656952019781026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree101.table
  base := (282936876147561421885624643493505063257/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-167314152183778905566002848204120000000000000)
      constant := (3804086240087701879456503824550604085591839125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (498685825460539640223/100000000000000000000)
  centralHi := (15583932045641863757/3125000000000000000)
  directionLo := (250586525994721234599/50000000000000000000)
  directionHi := (501173051989442469199/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree102.table
  base := (37008891469709019071583460683218427867543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-458394995678438231867599661757906120000000000000)
      constant := (10438430198197113042835204672650690810602444009406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree102.table
  base := (18504444662727829815994008062428102884099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-169066671208471389132865780981440000000000000)
      constant := (3886440358432765762511940969210047358541949382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250586525994721234599/50000000000000000000)
  centralHi := (501173051989442469199/100000000000000000000)
  directionLo := (503647995692988936363/100000000000000000000)
  directionHi := (125911998923247234091/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree103.table
  base := (38679369430889838129931852431616681765799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-463149181492650600583688147716234980000000000000)
      constant := (10662226976591697373187567100971417487556539675358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree103.table
  base := (19339683784290253267748930033882406061427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-170819190233163872699728713758760000000000000)
      constant := (3969678199677317653154954628142532469979384486) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503647995692988936363/100000000000000000000)
  centralHi := (125911998923247234091/25000000000000000000)
  directionLo := (253055418382376076843/50000000000000000000)
  directionHi := (506110836764752153687/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree104.table
  base := (8075709159329054405593784464546972581179/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-467903367306862969299776633674563840000000000000)
      constant := (10888402189490651826155510570069828632691676186590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree104.table
  base := (20189272089671879786203635242309717183593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-172571709257856356266591646536080000000000000)
      constant := (4053799763670094158233264621354284330517113874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253055418382376076843/50000000000000000000)
  centralHi := (506110836764752153687/100000000000000000000)
  directionLo := (254280875517541722929/50000000000000000000)
  directionHi := (508561751035083445859/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree105.table
  base := (21053210250072980138782889549957912099397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-472657553121075338015865119632892700000000000000)
      constant := (11116955836489776256801593418433977709383762220148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree105.table
  base := (8421283819147025596139874168601887492599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-174324228282548839833454579313400000000000000)
      constant := (4138805050274114545453575668585207847355755955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254280875517541722929/50000000000000000000)
  centralHi := (508561751035083445859/100000000000000000000)
  directionLo := (102200182023521425111/20000000000000000000)
  directionHi := (127750227529401781389/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree106.table
  base := (8772598696161910770608339334808721762851/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-477411738935287706731953605591221560000000000000)
      constant := (11347887917222653957290034399941177844661947289710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree106.table
  base := (21931496130682729900151247819173405017069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-176076747307241323400317512090720000000000000)
      constant := (4224694059364815178136089460735668103365410842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102200182023521425111/20000000000000000000)
  centralHi := (127750227529401781389/25000000000000000000)
  directionLo := (64178560193681429597/12500000000000000000)
  directionHi := (513428481549451436777/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree107.table
  base := (45648264683492464217398572070871122254001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-482165924749500075448042091549550420000000000000)
      constant := (11581198431355763159400643034262262843203783516242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree107.table
  base := (45648263624739358883052352131327252660313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-177829266331933806967180444868040000000000000)
      constant := (4311466790828442726189511075144541901126631417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64178560193681429597/12500000000000000000)
  centralHi := (513428481549451436777/100000000000000000000)
  directionLo := (515844628925539935681/100000000000000000000)
  directionHi := (257922314462769967841/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree108.table
  base := (47462234057792685471331817585286328021729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-486920110563712444164130577507879280000000000000)
      constant := (11816887378584260334168997543246490471166798250418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree108.table
  base := (47462233138628486620056929271321267262053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-179581785356626290534043377645360000000000000)
      constant := (4399123244560669789626798059400988679381875077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (515844628925539935681/100000000000000000000)
  centralHi := (257922314462769967841/50000000000000000000)
  directionLo := (64781189003405990491/12500000000000000000)
  directionHi := (518249512027247923929/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree109.table
  base := (49304901557448225494271307068088618390913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-491674296377924812880219063466208140000000000000)
      constant := (12054954758628341757847796625972967346473892424946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree109.table
  base := (12326225189882852503056109644017364966213/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-181334304381318774100906310422680000000000000)
      constant := (4487663420465401702952956652747697436841458068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64781189003405990491/12500000000000000000)
  centralHi := (518249512027247923929/100000000000000000000)
  directionLo := (520643286945710257103/100000000000000000000)
  directionHi := (32540205434106891069/6250000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree110.table
  base := (51176267139817844319899837512254389030837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-496428482192137181596307549424537000000000000000)
      constant := (12295400571230102891940681989892087010420647638554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree110.table
  base := (25588133223603926079144626010442195917373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-183086823406011257667769243200000000000000000)
      constant := (4577087318453747694493091082878133621562953914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520643286945710257103/100000000000000000000)
  centralHi := (32540205434106891069/6250000000000000000)
  directionLo := (261513053100024907093/50000000000000000000)
  directionHi := (523026106200049814187/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree111.table
  base := (53076330765432657155023557032562015150069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1634660000000000000000000000000000000000000000
      center := (10255635)
      previous := (8869887)
      next := (0)
      square := (138528662906374041944301822716340000000000000)
      linear := (-13545477513685122981416109064401780000000000000)
      constant := (338870940977049361344548574753780347368521179154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree111.table
  base := (53076330164276913562931873651066482496007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-184839342430703741234632175977320000000000000)
      constant := (4667394938443133357262040583228365859833679463) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261513053100024907093/50000000000000000000)
  centralHi := (523026106200049814187/100000000000000000000)
  directionLo := (262699059425390018249/50000000000000000000)
  directionHi := (525398118850780036499/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree112.table
  base := (55005092397608758046498060196873034444369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-505936853820561919028484521341194720000000000000)
      constant := (12783427493168639050560784428966636875593879249298) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree112.table
  base := (55005091875870302890455856687433420455033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-186591861455396224801495108754640000000000000)
      constant := (4758586280356534635699251702863180425785167897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262699059425390018249/50000000000000000000)
  centralHi := (525398118850780036499/100000000000000000000)
  directionLo := (131939867652155034383/25000000000000000000)
  directionHi := (527759470608620137533/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree113.table
  base := (28481276001056197423068482617126603999837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-510691039634774287744573007299523580000000000000)
      constant := (13031008602076486916817892381067380236258364273108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree113.table
  base := (14240637887333219556918327314287826824119/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-188344380480088708368358041531960000000000000)
      constant := (4850661344121816321318492388635487237817915484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (131939867652155034383/25000000000000000000)
  centralHi := (527759470608620137533/100000000000000000000)
  directionLo := (530110303938947767423/100000000000000000000)
  directionHi := (4141486749523029433/781250000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree114.table
  base := (58948709546870408274683652107987757523673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-515445225448986656460661493257852440000000000000)
      constant := (13280968142680383739494131504108003070540495032866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree114.table
  base := (58948709153963884013416648584330375248493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-190096899504781191935220974309280000000000000)
      constant := (4943620129671160445085143450193345798923921037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530110303938947767423/100000000000000000000)
  centralHi := (4141486749523029433/781250000000000000)
  directionLo := (266225379081050506691/50000000000000000000)
  directionHi := (532450758162101013383/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree115.table
  base := (60963565001719664567196072623549087556649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-520199411263199025176749979216181300000000000000)
      constant := (13533306114797895586100761174632339405421801861058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree115.table
  base := (60963564660793199797989029511998539873847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-191849418529473675502083907086600000000000000)
      constant := (5037462636940572010925824556585004774581328023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266225379081050506691/50000000000000000000)
  centralHi := (532450758162101013383/100000000000000000000)
  directionLo := (267390484774864780987/50000000000000000000)
  directionHi := (21391238781989182479/4000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree116.table
  base := (7875889792273760701548766292823349379673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-524953597077411393892838465174510160000000000000)
      constant := (13788022518256828534461832246629907922390497478928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree116.table
  base := (31503559021193858291733030594994621748347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-193601937554166159068946839863920000000000000)
      constant := (5132188865869451281064120728422446238884197046) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267390484774864780987/50000000000000000000)
  centralHi := (21391238781989182479/4000000000000000000)
  directionLo := (268550535708691789161/50000000000000000000)
  directionHi := (537101071417383578323/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree117.table
  base := (65079369529316632629016146349342402523903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-529707782891623762608926951132839020000000000000)
      constant := (14045117352894091504488961599595903736325976128526) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree117.table
  base := (32539684636341821629503954999684712666563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-195354456578858642635809772641240000000000000)
      constant := (5227798816400223340936186773241447060560875334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268550535708691789161/50000000000000000000)
  centralHi := (537101071417383578323/100000000000000000000)
  directionLo := (134852798553379578423/25000000000000000000)
  directionHi := (539411194213518313693/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree118.table
  base := (67180318549476246398591252591994010852677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-534461968705836131325015437091167880000000000000)
      constant := (14304590618554710033248433974698839460187616843834) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree118.table
  base := (67180318326841135540485825608773206536031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-197106975603551126202672705418560000000000000)
      constant := (5324292488478016974518382281560020013238092479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134852798553379578423/25000000000000000000)
  centralHi := (539411194213518313693/100000000000000000000)
  directionLo := (541711465605082583769/100000000000000000000)
  directionHi := (54171146560508258377/10000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree119.table
  base := (17327491343561575907802500324804441298857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-539216154520048500041103923049496740000000000000)
      constant := (14566442315090970184808065066699387759601125837576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree119.table
  base := (34654982590559073272392541242564745266851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-198859494628243609769535638195880000000000000)
      constant := (5421669882050386000245906824675611044588947718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (541711465605082583769/100000000000000000000)
  centralHi := (54171146560508258377/10000000000000000000)
  directionLo := (272001005279925008417/50000000000000000000)
  directionHi := (108800402111970003367/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree120.table
  base := (71468309980281627845026276532809036037979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-543970340334260868757192409007825600000000000000)
      constant := (14830672442361674682272940959643229989744418182918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree120.table
  base := (71468309812760833429607745624283036416873/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-200612013652936093336398570973200000000000000)
      constant := (5519930997067067179280124264164041227444872457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272001005279925008417/50000000000000000000)
  centralHi := (108800402111970003367/20000000000000000000)
  directionLo := (273141475712821654627/50000000000000000000)
  directionHi := (109256590285128661851/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree121.table
  base := (73655352345207505077250338940871948066867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-548724526148473237473280894966154460000000000000)
      constant := (15097281000231495840915330314813176737919843797814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree121.table
  base := (73655352199908228498193465636815864536547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-202364532677628576903261503750520000000000000)
      constant := (5619075833479769633978890988224086244761232323) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273141475712821654627/50000000000000000000)
  centralHi := (109256590285128661851/20000000000000000000)
  directionLo := (274277204003296802123/50000000000000000000)
  directionHi := (548554408006593604247/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree122.table
  base := (7587109244752650917416560874472985040139/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-553478711962685606189369380924483320000000000000)
      constant := (15366267988570412024980426058295485179851403856380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree122.table
  base := (37935546160754602232801539502599457134403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-204117051702321060470124436527840000000000000)
      constant := (5719104391241991424169776384645524401619792454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274277204003296802123/50000000000000000000)
  centralHi := (548554408006593604247/100000000000000000000)
  directionLo := (550816497636569490767/100000000000000000000)
  directionHi := (34426031102285593173/6250000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree123.table
  base := (195288825666343115939609710080464826553/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-558232897776897974905457866882812180000000000000)
      constant := (15637633407253216195270892522300326242392227930400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree123.table
  base := (61027757935351593471863007914259192957/7812500000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-205869570727013544036987369305160000000000000)
      constant := (5820016670308859538644315527689766153269776640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550816497636569490767/100000000000000000000)
  centralHi := (34426031102285593173/6250000000000000000)
  directionLo := (553069335249902967777/100000000000000000000)
  directionHi := (276534667624951483889/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree124.table
  base := (20097166445565847833965357695147631479469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-562987083591110343621546352841141040000000000000)
      constant := (15911377256159086701820825128915081283658586173992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree124.table
  base := (803886656874911260118557837958393267031/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-207622089751706027603850302082480000000000000)
      constant := (5921812670636990083283053806324369072687147900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553069335249902967777/100000000000000000000)
  centralHi := (276534667624951483889/50000000000000000000)
  directionLo := (555313033449533002701/100000000000000000000)
  directionHi := (277656516724766501351/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree125.table
  base := (41345249487695806272846989786471822690219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-567741269405322712337634838799469900000000000000)
      constant := (16187499535171211841840444033832535444623071089996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree125.table
  base := (41345249446605783483801789900627017979243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-209374608776398511170713234859800000000000000)
      constant := (6024492392184365897493028324005970165432295574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555313033449533002701/100000000000000000000)
  centralHi := (277656516724766501351/50000000000000000000)
  directionLo := (557547702572681001977/100000000000000000000)
  directionHi := (278773851286340500989/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree126.table
  base := (21255257456804294870639401769281577217727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-572495455219535081053723324757798760000000000000)
      constant := (16466000244176460878583165555030586760617998343736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree126.table
  base := (85021029755960586736231011108289882770929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-211127127801090994737576167637120000000000000)
      constant := (6128055834910229217587270648007172351040982161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557547702572681001977/100000000000000000000)
  centralHi := (278773851286340500989/50000000000000000000)
  directionLo := (111954690150833315707/20000000000000000000)
  directionHi := (69971681344270822317/12500000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree127.table
  base := (87380258319596211066864962144856523946589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-577249641033747449769811810716127620000000000000)
      constant := (16746879383065095228460424132625447857107765346538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree127.table
  base := (43690129128907411971020510523071164044101/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-212879646825783478304439100414440000000000000)
      constant := (6232502998774987338286865980142168402746838218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111954690150833315707/20000000000000000000)
  centralHi := (69971681344270822317/12500000000000000000)
  directionLo := (561990383987466420521/100000000000000000000)
  directionHi := (280995191993733210261/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree128.table
  base := (89768184434903668984018019882024172930481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-582003826847959818485900296674456480000000000000)
      constant := (17030136951730514394486258779335516367733398264402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree128.table
  base := (4488409219067035562444107910754031973893/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-214632165850475961871302033191760000000000000)
      constant := (6337833883740129509346255764268953132606592740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561990383987466420521/100000000000000000000)
  centralHi := (280995191993733210261/50000000000000000000)
  directionLo := (70524825772951726743/12500000000000000000)
  directionHi := (112839721236722762789/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree129.table
  base := (46092404077998161674189376552836002556999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-586758012662172187201988782632785340000000000000)
      constant := (17315772950069031973650698382355688564554697491516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree129.table
  base := (92184808109561254184207505673579877271399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-216384684875168445438164965969080000000000000)
      constant := (6444048489768153549975583860863697948892520391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70524825772951726743/12500000000000000000)
  centralHi := (112839721236722762789/20000000000000000000)
  directionLo := (283199109614015713731/50000000000000000000)
  directionHi := (566398219228031427463/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree130.table
  base := (94630129466180024863241762204785712503453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-591512198476384555918077268591114200000000000000)
      constant := (17603787377979677711023138882131844047363309579626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree130.table
  base := (47315064712963308931652410346110111234103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-218137203899860929005027898746400000000000000)
      constant := (6551146816822500874914520925737114471432267054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283199109614015713731/50000000000000000000)
  centralHi := (566398219228031427463/100000000000000000000)
  directionLo := (568589323035385309981/100000000000000000000)
  directionHi := (284294661517692654991/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree131.table
  base := (19420829669836141893279506157668280594189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-596266384290596924634165754549443060000000000000)
      constant := (17894180235364022128831834068828103688787794328690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree131.table
  base := (97104148314288012514215532408297612067017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-219889722924553412571890831523720000000000000)
      constant := (6659128864867498807556810475853489425056040553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (568589323035385309981/100000000000000000000)
  centralHi := (284294661517692654991/50000000000000000000)
  directionLo := (570772015602543662369/100000000000000000000)
  directionHi := (57077201560254366237/10000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree132.table
  base := (99606864789118640516833377066446652728413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-601020570104809293350254240507771920000000000000)
      constant := (18186951522126020736975672117910204955791402099946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree132.table
  base := (99606864758874439360526793660230817372531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-221642241949245896138753764301040000000000000)
      constant := (6767994633868309211605356531832889875575920979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570772015602543662369/100000000000000000000)
  centralHi := (57077201560254366237/10000000000000000000)
  directionLo := (286473196529859903059/50000000000000000000)
  directionHi := (572946393059719806119/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree133.table
  base := (51069139385242730827663870505117476562131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-605774755919021662066342726466100780000000000000)
      constant := (18482101238171875243171842102706036218354192647404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree133.table
  base := (102138278744271919170565289401575919228369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-223394760973938379705616697078360000000000000)
      constant := (6877744123790882606937392740737721205575467121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286473196529859903059/50000000000000000000)
  centralHi := (572946393059719806119/100000000000000000000)
  directionLo := (575112549719874867969/100000000000000000000)
  directionHi := (57511254971987486797/10000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree134.table
  base := (10469839027812369209230630650813325263933/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-610528941733234030782431212424429640000000000000)
      constant := (18779629383409909535494647482388304660209806557860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree134.table
  base := (104698390255404878020985389058071043820947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-225147279998630863272479629855680000000000000)
      constant := (6988377334601917050756248604629438935800471923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575112549719874867969/100000000000000000000)
  centralHi := (57511254971987486797/10000000000000000000)
  directionLo := (577270578126452015471/100000000000000000000)
  directionHi := (36079411132903250967/6250000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree135.table
  base := (107287199297208346558512701424977422859113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-615283127547446399498519698382758500000000000000)
      constant := (19079535957750458515389190558241480922988247329346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree135.table
  base := (107287199277519409747414738067134651185767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-226899799023323346839342562633000000000000000)
      constant := (7099894266268821164344825592279300444469359303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577270578126452015471/100000000000000000000)
  centralHi := (36079411132903250967/6250000000000000000)
  directionLo := (579420569099510600207/100000000000000000000)
  directionHi := (36213785568719412513/6250000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree136.table
  base := (6869044113326900351991360480493276242569/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-620037313361658768214608184341087360000000000000)
      constant := (19381820961105768122208000149632563105406528219168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree136.table
  base := (54952352898084086596543532207608471420489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-228652318048015830406205495410320000000000000)
      constant := (7212294918759680771087827008809374226735720402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (579420569099510600207/100000000000000000000)
  centralHi := (36213785568719412513/6250000000000000000)
  directionLo := (581562611780325280101/100000000000000000000)
  directionHi := (290781305890162640051/50000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree137.table
  base := (112550909811981899603036411652128700250507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-624791499175871136930696670299416220000000000000)
      constant := (19686484393389905116820456819461443939260526958694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree137.table
  base := (56275454898598357800897921684675351625351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-230404837072708313973068428187640000000000000)
      constant := (7325579292043228684846792641084535703480800718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (581562611780325280101/100000000000000000000)
  centralHi := (290781305890162640051/50000000000000000000)
  directionLo := (583696793674512087703/100000000000000000000)
  directionHi := (72962099209314010963/12500000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree138.table
  base := (115225811279542401302491753715084427866523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-629545684990083505646785156257745080000000000000)
      constant := (19993526254518675386961778106030723690168274802566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree138.table
  base := (115225811266731042093131883135676546178001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-232157356097400797539931360964960000000000000)
      constant := (7439747386088817250930898584432149490507204209) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583696793674512087703/100000000000000000000)
  centralHi := (72962099209314010963/12500000000000000000)
  directionLo := (292911600346870238281/50000000000000000000)
  directionHi := (585823200693740476563/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree139.table
  base := (7370588137641671944060034865690658759597/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-634299870804295874362873642216073940000000000000)
      constant := (20302946544409549705089718451185795726079399655584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree139.table
  base := (117929410191166275758070461325545263872769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-233909875122093281106794293742280000000000000)
      constant := (7554799200866393296248109227095689487894946721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292911600346870238281/50000000000000000000)
  centralHi := (585823200693740476563/100000000000000000000)
  directionLo := (293970958598043801069/50000000000000000000)
  directionHi := (587941917196087602139/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree140.table
  base := (30165426641693465318974067757531943382357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-639054056618508243078962128174402800000000000000)
      constant := (20614745262981596014362508541935996065227174665576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree140.table
  base := (120661706557156274081934808250424956716219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-235662394146785764673657226519600000000000000)
      constant := (7670734736346475191983503584833188729386127771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293970958598043801069/50000000000000000000)
  centralHi := (587941917196087602139/100000000000000000000)
  directionLo := (590053026025088467643/100000000000000000000)
  directionHi := (147513256506272116911/25000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree141.table
  base := (61711350179968233731247605374636762237889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1286860000000000000000000000000000000000000000
      center := (8073585)
      previous := (6982677)
      next := (0)
      square := (109054479309273181956152498734140000000000000)
      linear := (-13698047711334481102022353492185780000000000000)
      constant := (445296221492668456237796134638548027770689967708) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree141.table
  base := (15427837543950510702645858660022622792087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 470000000000000000000000000000000000000000
      center := (2925)
      previous := (2574)
      next := (0)
      square := (39829977833920081065066654030000000000000)
      linear := (-5051381131308047834904684240360000000000000)
      constant := (165692638138300676008473657765248506169824712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590053026025088467643/100000000000000000000)
  centralHi := (147513256506272116911/25000000000000000000)
  directionLo := (592156608547533079511/100000000000000000000)
  directionHi := (74019576068441634939/12500000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree142.table
  base := (63106195784435856460153069314108744331709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-648562428246932980511139100091060520000000000000)
      constant := (21245477985853095356289674562489516620068608611156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree142.table
  base := (126212391561653146543953055264084062591351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-239167432196170731807383092074240000000000000)
      constant := (7905256969298962887987907999062201694264294359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592156608547533079511/100000000000000000000)
  centralHi := (74019576068441634939/12500000000000000000)
  directionLo := (297126372345029701767/50000000000000000000)
  directionHi := (118850548938011880707/20000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree143.table
  base := (64515390090466233200569719400696070839179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-653316614061145349227227586049389380000000000000)
      constant := (21564411989998136843307464386727282154768995346636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree143.table
  base := (16128847521834891268524567121299075113997/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-240919951220863215374246024851560000000000000)
      constant := (8023843666715081401067509941346837255414554984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297126372345029701767/50000000000000000000)
  centralHi := (118850548938011880707/20000000000000000000)
  directionLo := (119268302594917736623/20000000000000000000)
  directionHi := (149085378243647170779/25000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree144.table
  base := (131877866183699287849961894792371351017811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-658070799875357717943316072007718240000000000000)
      constant := (21885724422515426125272453589437241364822667238262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree144.table
  base := (131877866178282374099177233953915839808681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-242672470245555698941108957628880000000000000)
      constant := (8143314084721096457539671084117160090137376329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119268302594917736623/20000000000000000000)
  centralHi := (149085378243647170779/25000000000000000000)
  directionLo := (149605747638161892067/25000000000000000000)
  directionHi := (598422990552647568269/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree145.table
  base := (8422103097810810466322121697672061629779/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-662824985689570086659404557966047100000000000000)
      constant := (22209415283331179429071482115202554071013084776288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree145.table
  base := (526381443594846953695831872187283725771/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-244424989270248182507971890406200000000000000)
      constant := (8263668223290097890728457756434397696058403584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149605747638161892067/25000000000000000000)
  centralHi := (598422990552647568269/100000000000000000000)
  directionLo := (600497253238619501019/100000000000000000000)
  directionHi := (30024862661930975051/5000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree146.table
  base := (137658130312767573480468604115975499522021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-667579171503782455375493043924375960000000000000)
      constant := (22535484572372902938859379629865601267180067337082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree146.table
  base := (137658130308703409707637608992056904284577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-246177508294940666074834823183520000000000000)
      constant := (8384906082395641632227499694658813701564630593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (600497253238619501019/100000000000000000000)
  centralHi := (30024862661930975051/5000000000000000000)
  directionLo := (75320546942745737911/12500000000000000000)
  directionHi := (602564375541965903289/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree147.table
  base := (1757391355191299407820635516321578304013/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-672333357317994824091581529882704820000000000000)
      constant := (22863932289569353485029973440463992377369615611680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree147.table
  base := (140591308411783886154040835837876752213369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-247930027319633149641697755960840000000000000)
      constant := (8507027662011736021141899281709909745639332121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75320546942745737911/12500000000000000000)
  centralHi := (602564375541965903289/100000000000000000000)
  directionLo := (604624430698455911249/100000000000000000000)
  directionHi := (483699544558764729/80000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree148.table
  base := (143553183861003634323093059199390790926021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1634660000000000000000000000000000000000000000
      center := (10255635)
      previous := (8869887)
      next := (0)
      square := (138528662906374041944301822716340000000000000)
      linear := (-18299663327897491697504595022730640000000000000)
      constant := (626885363104067612853086647891496975029512948786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree148.table
  base := (143553183857954961028132683177764607558757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-249682546344325633208560688738160000000000000)
      constant := (8630032962112828917269679723370722018097294213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604624430698455911249/100000000000000000000)
  centralHi := (483699544558764729/80000000000000000)
  directionLo := (303338745350220844891/50000000000000000000)
  directionHi := (606677490700441689783/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree149.table
  base := (29308751327696619256232362978671831124773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-681841728946419561523758501799362540000000000000)
      constant := (23527963008147497212829883586455572871128796495330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree149.table
  base := (36635939158960701743976304144063290286509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-251435065369018116775423621515480000000000000)
      constant := (8753921982673795535985837492473303232971593524) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303338745350220844891/50000000000000000000)
  centralHi := (606677490700441689783/100000000000000000000)
  directionLo := (608723626326214736851/100000000000000000000)
  directionHi := (152180906581553684213/25000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree150.table
  base := (9347689171034272148851581805935905042789/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-686595914760631930239846987757691400000000000000)
      constant := (23863546009392636171935783748447480743004931631008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree150.table
  base := (149563026734261844931037675800270121427721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-253187584393710600342286554292800000000000000)
      constant := (8878694723669926933132870029662796698233835689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608723626326214736851/100000000000000000000)
  centralHi := (152180906581553684213/25000000000000000000)
  directionLo := (610762907168477045447/100000000000000000000)
  directionHi := (76345363396059630681/12500000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree151.table
  base := (152610994144189844588296244928323010683339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-691350100574844298955935473716020260000000000000)
      constant := (24201507438519330045276548932758686527781419640038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree151.table
  base := (76305497071104898607715220151437481556203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-254940103418403083909149487070120000000000000)
      constant := (9004351185076919077319855273151010793515304854) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610762907168477045447/100000000000000000000)
  centralHi := (76345363396059630681/12500000000000000000)
  directionLo := (122559080332391905097/20000000000000000000)
  directionHi := (306397700830979762743/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree152.table
  base := (155687658850577568649347944635378302773311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-696104286389056667672023959674349120000000000000)
      constant := (24541847295462076382565554446623683656722256069262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree152.table
  base := (155687658848862981774806296788274858897709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-256692622443095567476012419847440000000000000)
      constant := (9130891366870862454888894858767539163305039181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122559080332391905097/20000000000000000000)
  centralHi := (306397700830979762743/50000000000000000000)
  directionLo := (614821177110218695523/100000000000000000000)
  directionHi := (153705294277554673881/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree153.table
  base := (6351720833802259155810666559358474851279/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-700858472203269036388112445632677980000000000000)
      constant := (24884565580156430876976045143809800861286235037950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree153.table
  base := (79396510421785912920694297803142896706503/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-258445141467788051042875352624760000000000000)
      constant := (9258315269028232159595970167435125317649330254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (614821177110218695523/100000000000000000000)
  centralHi := (153705294277554673881/25000000000000000000)
  directionLo := (123368059942328266037/20000000000000000000)
  directionHi := (308420149855820665093/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree154.table
  base := (161927080117142080484232000745267796987043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-705612658017481405104200931591006840000000000000)
      constant := (25229662292538980766456939511099880570984506928406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree154.table
  base := (20240885014482072496529801032154010340141/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-260197660492480534609738285402080000000000000)
      constant := (9386622891525878424921629106097985670730971752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123368059942328266037/20000000000000000000)
  centralHi := (308420149855820665093/50000000000000000000)
  directionLo := (618852834584685490031/100000000000000000000)
  directionHi := (38678302161542843127/6250000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree155.table
  base := (82544918328258116043246831884391582032063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-710366843831693773820289417549335700000000000000)
      constant := (25577137432547319435255705988045162246785537566492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree155.table
  base := (82544918327701607854941555741329356367089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-261950179517173018176601218179400000000000000)
      constant := (9515814234341017562003314649978193096429799202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618852834584685490031/100000000000000000000)
  centralHi := (38678302161542843127/6250000000000000000)
  directionLo := (620858845792385162673/100000000000000000000)
  directionHi := (310429422896192581337/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree156.table
  base := (42070322613255782071378603902772275465147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-715121029645906142536377903507664560000000000000)
      constant := (25926991000120022114508216560576387251615486486296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree156.table
  base := (84140645226029746050575151951405354939947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-263702698541865501743464150956720000000000000)
      constant := (9645889297451223270575468964427868858124685846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620858845792385162673/100000000000000000000)
  centralHi := (310429422896192581337/50000000000000000000)
  directionLo := (155714599091536150967/25000000000000000000)
  directionHi := (622858396366144603869/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree157.table
  base := (85750720748332724477466088437591722224113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-719875215460118511252466389465993420000000000000)
      constant := (26279222995196622592738762792877272411416427318692) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree157.table
  base := (171501441495831178033439145819788337467957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-265455217566557985310327083734040000000000000)
      constant := (9776848080834418294110356794554352437466717013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155714599091536150967/25000000000000000000)
  centralHi := (622858396366144603869/100000000000000000000)
  directionLo := (624851548328847382023/100000000000000000000)
  directionHi := (78106443541105922753/12500000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree158.table
  base := (21843786222200082823583419419212850448533/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-724629401274330879968554875424322280000000000000)
      constant := (26633833417717590857505950840016369772180289031888) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree158.table
  base := (87375144888439209420916988561481120586317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-267207736591250468877190016511360000000000000)
      constant := (9908690584468866393653179447173263590750348506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (624851548328847382023/100000000000000000000)
  centralHi := (78106443541105922753/12500000000000000000)
  directionLo := (156709590679326023979/25000000000000000000)
  directionHi := (626838362717304095917/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree159.table
  base := (178027835286137472052827257535989068659891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-729383587088543248684643361382651140000000000000)
      constant := (26990822267624311598450091289609389501609636461622) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree159.table
  base := (178027835285512236937127046285555753030991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-268960255615942952444052949288680000000000000)
      constant := (10041416808333164617709376999161952658445459119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156709590679326023979/25000000000000000000)
  centralHi := (626838362717304095917/100000000000000000000)
  directionLo := (25152755984162470037/4000000000000000000)
  directionHi := (314409449802030875463/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree160.table
  base := (181334078012732392523567252982802769433817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-734137772902755617400731847340980000000000000000)
      constant := (27350189544859063509833244446359244987805928199714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree160.table
  base := (181334078012191157331245975584679667491743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-270712774640635436010915882066000000000000000)
      constant := (10175026752406235848030297568130557385489260287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25152755984162470037/4000000000000000000)
  centralHi := (314409449802030875463/50000000000000000000)
  directionLo := (630793218118596840797/100000000000000000000)
  directionHi := (315396609059298420399/50000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree161.table
  base := (92334508973993226250746847965555194873699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-738891958716967986116820333299308860000000000000)
      constant := (27711935249364999337475974687428834870906581974316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree161.table
  base := (92334508973758974958081403962397741454113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-272465293665327919577778814843320000000000000)
      constant := (10309520416667321603307307396855033221744271234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630793218118596840797/100000000000000000000)
  centralHi := (315396609059298420399/50000000000000000000)
  directionLo := (158190344116978321927/25000000000000000000)
  directionHi := (632761376467913287709/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree162.table
  base := (23504081885330251221705390640907668260777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-743646144531180354832908819257637720000000000000)
      constant := (28076059381086126620924863461998457038375187232272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree162.table
  base := (47008163770559120301322163222054676663241/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-274217812690020403144641747620640000000000000)
      constant := (10444897801095975084668531626402715122996397476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158190344116978321927/25000000000000000000)
  centralHi := (632761376467913287709/100000000000000000000)
  directionLo := (634723431956565540687/100000000000000000000)
  directionHi := (39670214497285346293/6250000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree163.table
  base := (9571249470378983752420801299325447209403/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-748400330345392723548997305215966580000000000000)
      constant := (28442561939967289086852108338777033974613880390520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree163.table
  base := (95712494703614334494984039553224955970889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-275970331714712886711504680397960000000000000)
      constant := (10581158905672054448515050408880587855479387602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634723431956565540687/100000000000000000000)
  centralHi := (39670214497285346293/6250000000000000000)
  directionLo := (127335888201225263829/20000000000000000000)
  directionHi := (318339720503063159573/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree164.table
  base := (38969204182763067346840021011057039673409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-753154516159605092265085791174295440000000000000)
      constant := (28811442925954148654196632996782370738741892984890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree164.table
  base := (194846020913511534012896806922492345909583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-277722850739405370278367613175280000000000000)
      constant := (10718303730375716293667478590526345592114268847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127335888201225263829/20000000000000000000)
  centralHi := (318339720503063159573/50000000000000000000)
  directionLo := (638629459174117712387/100000000000000000000)
  directionHi := (159657364793529428097/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree165.table
  base := (24786968699062160122948132219535317400527/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-757908701973817460981174277132624300000000000000)
      constant := (29182702338993168015494548840637203442481585788272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree165.table
  base := (198295749592234343327977806578392892251611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-279475369764097853845230545952600000000000000)
      constant := (10856332275187409351047887832604669898983808699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638629459174117712387/100000000000000000000)
  centralHi := (159657364793529428097/25000000000000000000)
  directionLo := (640573541172423605449/100000000000000000000)
  directionHi := (12811470823448472109/2000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree166.table
  base := (25221771929362925211842378331511658561761/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-762662887788029829697262763090953160000000000000)
      constant := (29556340179031593762292300153250590474423219793296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree166.table
  base := (50443543858668960128332785955894271617387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-281227888788790337412093478729920000000000000)
      constant := (10995244540087868365220345360356041784011231532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (640573541172423605449/100000000000000000000)
  centralHi := (12811470823448472109/2000000000000000000)
  directionLo := (642511740885200694773/100000000000000000000)
  directionHi := (321255870442600347387/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree167.table
  base := (25660162304054811957586988318566450672113/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-767417073602242198413351249049282020000000000000)
      constant := (29932356446017440025554979844610639238968016602768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree167.table
  base := (205281298432241558340444849879010420801103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-282980407813482820978956411507240000000000000)
      constant := (11135040525058108158077068234747574019549636527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642511740885200694773/100000000000000000000)
  centralHi := (321255870442600347387/50000000000000000000)
  directionLo := (3222220556931523411/500000000000000000)
  directionHi := (644444111386304682201/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree168.table
  base := (208817118576631638495419763941001728908599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-772171259416454567129439735007610880000000000000)
      constant := (30310751139899472604632141168185646098857602632958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree168.table
  base := (10440855928823060494298398166002891909299/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-284732926838175304545819344284560000000000000)
      constant := (11275720230079417865804374181992247764552829820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell029.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3222220556931523411/500000000000000000)
  centralHi := (644444111386304682201/100000000000000000000)
  directionLo := (323185352478123795539/50000000000000000000)
  directionHi := (646370704956247591079/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 1613
  qDenominator := 3478
  table := BinomialMassData.Q1613_3478.Degree169.table
  base := (13273852241195852334422469137433460719867/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 60482420000000000000000000000000000000000000000
      center := (379458495)
      previous := (328185819)
      next := (0)
      square := (5125560527535839551939167440504580000000000000)
      linear := (-776925445230666935845528220965939740000000000000)
      constant := (30691524260627193560673497063181517574299997181024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1613_3478.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 22
  qDenominator := 47
  table := BinomialMassData.Q22_47.Degree169.table
  base := (106190817929493077205250908549397447200291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 22090000000000000000000000000000000000000000
      center := (137475)
      previous := (120978)
      next := (0)
      square := (1872008958194243810058132739410000000000000)
      linear := (-286485445862867788112682277061880000000000000)
      constant := (11417283655133355341008931546581197921730885638) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22_47.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell029.Kernel169
