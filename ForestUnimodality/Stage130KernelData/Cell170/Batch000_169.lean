import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell170.Parameters
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch000_049
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch050_099
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch100_149
import ForestUnimodality.BinomialMassData.Q95599_180624.Batch150_199
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch000_049
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch050_099
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch100_149
import ForestUnimodality.BinomialMassData.Q11953_22578.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree000.table
  base := (189836534445653951466681519/2500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (175859125299253037100211117500000000000)
      linear := (-12368570953170197456588708000000000000)
      constant := (189836534445653951466681519000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree000.table
  base := (189836534445653951466681519/2500000000000000000000000)
  polynomial :=
    { denominator := 2500000000000000000000000000000000000000
      center := (38)
      previous := (19)
      next := (19)
      square := (175859125299253037100211117500000000000)
      linear := (-12368570953170197456588708000000000000)
      constant := (189836534445653951466681519000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree001.table
  base := (206918592300004265388350304587198561832591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-5622231475205397528976934196388624625000000000)
      constant := (2931582774583324502138916232671291131243157017879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree001.table
  base := (51718389945079551528652375728350957005229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-8435415206209662197148551589692788500000000000)
      constant := (4396418827135976899771129596799985274159659142206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49913435199935546641/100000000000000000000)
  directionHi := (24956717599967773321/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree002.table
  base := (30080018314893090762635302133340214434603/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-16341271260660049341684803782850917875000000000)
      constant := (2564555905185410761535413678645329105661620067442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree002.table
  base := (240550136499948890576818575180962440727841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-21793876329950908198734805830760828000000000000)
      constant := (3418139348674106862095908447805947429358711565129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49913435199935546641/100000000000000000000)
  centralHi := (24956717599967773321/50000000000000000000)
  directionLo := (70588257004379487127/100000000000000000000)
  directionHi := (8823532125547435891/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree003.table
  base := (150997043385037331744069771453286639406009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-32332260411349336519872275028158531750000000000)
      constant := (2164368614647558142682481369280933985892084555521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree003.table
  base := (75463778597877147615551615804064827534643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-16170266192477800067302438104298969000000000000)
      constant := (1081699052707938789259485416544500535596398234667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70588257004379487127/100000000000000000000)
  centralHi := (8823532125547435891/12500000000000000000)
  directionLo := (17290521149317037967/20000000000000000000)
  directionHi := (21613151436646297459/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree004.table
  base := (51185199864723615403434251659156509431071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-21438079570909303625415739172924586500000000000)
      constant := (747854965452030179242970264563037619181559210999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree004.table
  base := (20464124443506942926762302996659082567799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-128661565319880876211424839759305144000000000000)
      constant := (4485086441320411891315972990076550604174816970465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17290521149317037967/20000000000000000000)
  centralHi := (21613151436646297459/25000000000000000000)
  directionLo := (49913435199935546641/50000000000000000000)
  directionHi := (99826870399871093283/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree005.table
  base := (74280123266608697201905297985224439225067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-160260173616863633945372044990619442750000000000)
      constant := (3370290763344046060949546346056080577579345768969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree005.table
  base := (74244711533133394726525902728487679740197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-53433844494964984006345016964272158000000000000)
      constant := (1122965792190760945896340946350095137039065613293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49913435199935546641/50000000000000000000)
  centralHi := (99826870399871093283/100000000000000000000)
  directionLo := (55804917048793344467/50000000000000000000)
  directionHi := (22321966819517337787/20000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree006.table
  base := (56790046547531089608606759532614257609279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-63963956602757148712749884981230455500000000000)
      constant := (906831774989416767656503664807760067400676608151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree006.table
  base := (28382068438662964869158446166494392389639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-31990250274984837971107543671054634000000000000)
      constant := (453259007850427058125541819712524672789602088991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/50000000000000000000)
  centralHi := (22321966819517337787/20000000000000000000)
  directionLo := (122262447549314949813/100000000000000000000)
  directionHi := (61131223774657474907/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree007.table
  base := (22509571046749862940204409408461288530429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-37253927666613209721854544149460548375000000000)
      constant := (388399159268010399264637594546390730247855032501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree007.table
  base := (11249832522259859362716148136188133948539/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-55895367453730775908563868289959783500000000000)
      constant := (582442480871954180980785889794837862642848629273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122262447549314949813/100000000000000000000)
  centralHi := (61131223774657474907/50000000000000000000)
  directionLo := (26411707323993391579/20000000000000000000)
  directionHi := (16507317077495869737/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree008.table
  base := (9130368603528838014643629342994521325753/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-63788815547771767631001218712458803500000000000)
      constant := (524021268885507099553896747335093355265299596771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree008.table
  base := (18252810482586728445016654088917100593311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-42536906329989529906977614048891744000000000000)
      constant := (349282362675424234847283757244417363391284029559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26411707323993391579/20000000000000000000)
  centralHi := (16507317077495869737/12500000000000000000)
  directionLo := (28235302801751794851/20000000000000000000)
  directionHi := (8823532125547435891/6250000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree009.table
  base := (7508367787487372544595940747220639557621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-23898913198541240226406873733575594812500000000)
      constant := (163657374192536694722763135874051737461107972949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree009.table
  base := (3002030094653896909763032031459450453203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-47810234357491875874912649237810299000000000000)
      constant := (327281050834859895009714894634466420072405356535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28235302801751794851/20000000000000000000)
  centralHi := (8823532125547435891/6250000000000000000)
  directionLo := (37435076399951659981/25000000000000000000)
  directionHi := (5989612223992265597/4000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree010.table
  base := (24873119198661105723270733192918464278633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-106139551524634231636586698251993020500000000000)
      constant := (634944312515069392597440484375030414749656368977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree010.table
  base := (6215471571951442203060362505133657402693/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-79625343577491332764271526640093281000000000000)
      constant := (476199133835943151231990543518501241730701805351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37435076399951659981/25000000000000000000)
  centralHi := (5989612223992265597/4000000000000000000)
  directionLo := (7892007053750910173/5000000000000000000)
  directionHi := (157840141075018203461/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree011.table
  base := (645323947359246561089379518414517317961/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-87512587691327626775659426177262746312500000000)
      constant := (475587200033170198983091515592274190432561014816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree011.table
  base := (4128125877220309068204317562727543725187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-116713780824993135621565439231294818000000000000)
      constant := (634156063761444899733046479667180006017687383015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7892007053750910173/5000000000000000000)
  centralHi := (157840141075018203461/100000000000000000000)
  directionLo := (165544136555904067731/100000000000000000000)
  directionHi := (41386034138976016933/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree012.table
  base := (17126368750051784764733534715300331649507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-127227348985572773098505104887374303000000000000)
      constant := (648763291487332436268071401549350057288067886683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree012.table
  base := (8558927438555145758421925344067350620943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-63630218439998913778717754804565964000000000000)
      constant := (324427037057715326699439573195774940174807819367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165544136555904067731/100000000000000000000)
  centralHi := (41386034138976016933/25000000000000000000)
  directionLo := (17290521149317037967/10000000000000000000)
  directionHi := (172905211493170379671/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree013.table
  base := (221002465894285683295466810731945522777/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-34442811929010510957366077051266236062500000000)
      constant := (169165670933934978390612989963074556873785084008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree013.table
  base := (14136684962845518122537343254841052667421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-413421278805007558479916739960907114000000000000)
      constant := (2030414380134134746825003432816812906225746462447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17290521149317037967/10000000000000000000)
  centralHi := (172905211493170379671/100000000000000000000)
  directionLo := (89982724973958394813/50000000000000000000)
  directionHi := (179965449947916789627/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree014.table
  base := (2898439111736270430036065264836447401359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-111236359834883485920317633642066689125000000000)
      constant := (537192862168049387420211220168804764383875309013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree014.table
  base := (5793595710838996633151658745124247658811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-74176874495003605714587825182403074000000000000)
      constant := (358225809676574153716676243654025043846618099059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89982724973958394813/50000000000000000000)
  centralHi := (179965449947916789627/100000000000000000000)
  directionLo := (46689743378775324503/25000000000000000000)
  directionHi := (186758973515101298013/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree015.table
  base := (2348514559454925090587283507821436086261/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-39714761294245146322845678710111556687500000000)
      constant := (191599552150501850236069015514293902185013713109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree015.table
  base := (73346053078888744045956053100710215687/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-39725101261252975841261430185660814500000000000)
      constant := (191661613297912792628451764380100995947939875296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46689743378775324503/25000000000000000000)
  centralHi := (186758973515101298013/100000000000000000000)
  directionLo := (193313903281353441673/100000000000000000000)
  directionHi := (96656951640676720837/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree016.table
  base := (1870744465783094960152592526778584167101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-42350735976862464005585479539534217000000000000)
      constant := (206551680537676897763380550293135966886874400069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree016.table
  base := (1869481423911987129255664773922744513873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-127085295825012446475686843340360276000000000000)
      constant := (619882786439938715664240737699440421780793573611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193313903281353441673/100000000000000000000)
  centralHi := (96656951640676720837/50000000000000000000)
  directionLo := (39930748159948437313/20000000000000000000)
  directionHi := (99826870399871093283/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree017.table
  base := (5811773608220913315550454944197485193747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-539840527913757380259903364427482527750000000000)
      constant := (2684977497859599380388435759038665894225678289729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree017.table
  base := (1161470603631122051159265134820759690743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-179993717155021287236785861498317478000000000000)
      constant := (895353364810663393313542684609207503146543077835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39930748159948437313/20000000000000000000)
  centralHi := (99826870399871093283/50000000000000000000)
  directionLo := (205798365466756811823/100000000000000000000)
  directionHi := (12862397841672300739/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree018.table
  base := (4341544867050060045915628254453210650829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-190490741368388397484260324793518150500000000000)
      constant := (972204700853822579320306700013480388002088630101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree018.table
  base := (867536847453700272626000379844319743663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-190540373210025979172655931876154588000000000000)
      constant := (972624677146222110098790812668315820301523795235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205798365466756811823/100000000000000000000)
  centralHi := (12862397841672300739/6250000000000000000)
  directionLo := (211764771013138461383/100000000000000000000)
  directionHi := (26470596376642307673/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree019.table
  base := (3040917142498399954480237151190642971509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-201034640098857668215219528111208791750000000000)
      constant := (1057399058671046626812498246163438566406167125021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree019.table
  base := (1518775865668655886882759309823605690501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-301630543897546006662789003380987547000000000000)
      constant := (1586820222154368222975912995943312554550567564007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211764771013138461383/100000000000000000000)
  centralHi := (26470596376642307673/12500000000000000000)
  directionLo := (217567619961484922237/100000000000000000000)
  directionHi := (108783809980742461119/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree020.table
  base := (1884415009640076132008870784669491796693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-634735616487980816838536194286698299000000000000)
      constant := (3450644509247724968904386439138021147080859563351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree020.table
  base := (117592894670833732974649498990618881589/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-52908421330008840761099018157957202000000000000)
      constant := (287689782426984680198815662204859761111564914164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217567619961484922237/100000000000000000000)
  centralHi := (108783809980742461119/50000000000000000000)
  directionLo := (55804917048793344467/25000000000000000000)
  directionHi := (223219668195173377869/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree021.table
  base := (106407696225460710439976919702195266427/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-55530609389949052419284483686647518562500000000)
      constant := (312589457422981181831792020345544953933697067326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree021.table
  base := (212179226501736992780360638190040065929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-55545085343760013745066535752416479500000000000)
      constant := (312741874984415549508641296424364592825325782001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/25000000000000000000)
  centralHi := (223219668195173377869/100000000000000000000)
  directionLo := (45746418999795584927/20000000000000000000)
  directionHi := (57183023749744481159/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree022.table
  base := (-9442387741886319745385848051293035301/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-58166584072566370102024284516070178875000000000)
      constant := (339396843332464042068823609953592314489167248262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree022.table
  base := (-19436741646533620221241771964970902629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-174545248072533560187102160040627271000000000000)
      constant := (1018698503130595483826879838497951334316072447097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45746418999795584927/20000000000000000000)
  centralHi := (57183023749744481159/25000000000000000000)
  directionLo := (29264345386087900183/12500000000000000000)
  directionHi := (46822952617740640293/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree023.table
  base := (-181984026383128404995660872282960245093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-729630705062204253417169024145914070250000000000)
      constant := (4415118515718115620272847216798460712583337989245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree023.table
  base := (-911833340929857934224427283062292655171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-243273653485049438852006283765340138000000000000)
      constant := (1472453419047058923281362566302163739975319916101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29264345386087900183/12500000000000000000)
  centralHi := (46822952617740640293/20000000000000000000)
  directionLo := (119688212984338804363/50000000000000000000)
  directionHi := (239376425968677608727/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree024.table
  base := (-103957673365378512709952879860203271713/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-63438533437801005467503886174915499500000000000)
      constant := (398138053833598361826986451409404678567764002012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree024.table
  base := (-416244690480699088268282659713767965821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-63455077385013532696969088535794312000000000000)
      constant := (398342950286979284344849674383630121977188416251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119688212984338804363/50000000000000000000)
  centralHi := (239376425968677608727/100000000000000000000)
  directionLo := (244524895098629899627/100000000000000000000)
  directionHi := (61131223774657474907/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree025.table
  base := (-2345154832207128748898046460881042057279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-264298032481673292600974748017352639250000000000)
      constant := (1719992287513553866185802186149686676471259179849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree025.table
  base := (-469317343175607416125680395015571781497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-793100896785176468171239273563043074000000000000)
      constant := (5162659986563958351115539175692544601635571105105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244524895098629899627/100000000000000000000)
  centralHi := (61131223774657474907/25000000000000000000)
  directionLo := (249567175999677733207/100000000000000000000)
  directionHi := (31195896999959716651/12500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree026.table
  base := (-2963161135372544474816180251458492409773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-824525793636427689995801854005129841500000000000)
      constant := (5561750161094617273849706091134853961508441205089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree026.table
  base := (-2964398105032202594367659276398854349977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-274913621650063514659616494898851468000000000000)
      constant := (1854888389683382809988426717044605748997940533887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249567175999677733207/100000000000000000000)
  centralHi := (31195896999959716651/12500000000000000000)
  directionLo := (63627395018730083967/25000000000000000000)
  directionHi := (254509580074920335869/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree027.table
  base := (-3523724215141288829764290229929001251123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-285385829942611834062893154652733921750000000000)
      constant := (1994235136159427614618811414593845839618824380213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree027.table
  base := (-3524791918660816299922849085486780724481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-285460277705068206595486565276688578000000000000)
      constant := (1995286656067916617241935758132638311175406602711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63627395018730083967/25000000000000000000)
  centralHi := (254509580074920335869/100000000000000000000)
  directionLo := (129678908619877784753/50000000000000000000)
  directionHi := (259357817239755569507/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree028.table
  base := (-1008027266099860321698082214916608005771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-73982432168270276198463089492606140750000000000)
      constant := (535218245427042188276678016618257504325279664701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree028.table
  base := (-2016514987192785298016955994488428809161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-444010400640109347797034953481788532000000000000)
      constant := (3213010429672225794550300854107348054553434475373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129678908619877784753/50000000000000000000)
  centralHi := (259357817239755569507/100000000000000000000)
  directionLo := (264117073239933915791/100000000000000000000)
  directionHi := (16507317077495869737/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree029.table
  base := (-898532561296001857183647280174579150529/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-919420882210651126574434683864345612750000000000)
      constant := (6881306103030109834354077766698413961752306308985) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree029.table
  base := (-4493456565597855288548876659031227524411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-306553589815077590467226706032362798000000000000)
      constant := (2294987764895476884567535876546725391476888614541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264117073239933915791/100000000000000000000)
  centralHi := (16507317077495869737/6250000000000000000)
  directionLo := (268792074641881472689/100000000000000000000)
  directionHi := (26879207464188147269/10000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree030.table
  base := (-1227244464823130257170078518188684475751/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-79254381533504911563942691151451461375000000000)
      constant := (613217856205078410902176144159075462959126938081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree030.table
  base := (-98193232004944033787454312515888270319/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-158550122935041141201548388205099954000000000000)
      constant := (1227089128853317937498287778295457167679131902225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268792074641881472689/100000000000000000000)
  centralHi := (26879207464188147269/10000000000000000000)
  directionLo := (68346785953942699777/25000000000000000000)
  directionHi := (273387143815770799109/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree031.table
  base := (-5284025457506991069282556682513363706299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-327561424864488916986729967923496486750000000000)
      constant := (2618139079953933784258759802738427295933777295469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree031.table
  base := (-5284614096049282803764266258721975568899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-982940705775260923016900540364111054000000000000)
      constant := (7858609169267028731852349750927378102291557048207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68346785953942699777/25000000000000000000)
  centralHi := (273387143815770799109/100000000000000000000)
  directionLo := (277906245732626726711/100000000000000000000)
  directionHi := (34738280716578340839/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree032.table
  base := (-1405066263503565043348773948788246262829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-253578992696218640788266878430890346000000000000)
      constant := (2092152630106736392205659854494865145114168825697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree032.table
  base := (-2810385777333995727082292118556586763061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-169096778990045833137418458582937064000000000000)
      constant := (1395513681201859743933253308372036583371893282691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277906245732626726711/100000000000000000000)
  centralHi := (34738280716578340839/12500000000000000000)
  directionLo := (282353028017517948511/100000000000000000000)
  directionHi := (8823532125547435891/3125000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree033.table
  base := (-369983378760963380876163502891308928809/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-87162305581356864612162093639719442312500000000)
      constant := (741758963824065591342270658711215095690781740116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree033.table
  base := (-2960084837664163789123268674685633226887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-174370107017548179105353493771855619000000000000)
      constant := (1484311174902853219300654190648654672385264736097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282353028017517948511/100000000000000000000)
  centralHi := (8823532125547435891/3125000000000000000)
  directionLo := (286730855409946141493/100000000000000000000)
  directionHi := (143365427704973070747/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree034.table
  base := (-6184121537008612569273646717831958684587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-359193121055896729179607577876568410500000000000)
      constant := (3150612208026306857582585852291053949518980384797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree034.table
  base := (-3092248010318523530989345748582248375713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-538930305135151575219865586882322522000000000000)
      constant := (4728446183684891028402193383170362310799785273509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286730855409946141493/100000000000000000000)
  centralHi := (143365427704973070747/50000000000000000000)
  directionLo := (72760709889325573661/25000000000000000000)
  directionHi := (58208567911460458929/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree035.table
  base := (-1603707192316539116892963065639692041587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-277302764839774499932925085895694288812500000000)
      constant := (2505184541927654222109375146082734438970222280391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree035.table
  base := (-1603787641737468696439604973534039256817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-92458381536276435520611782074846364500000000000)
      constant := (835508214113647290110759161832901906245836877927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72760709889325573661/25000000000000000000)
  centralHi := (58208567911460458929/20000000000000000000)
  directionLo := (295291864891391429273/100000000000000000000)
  directionHi := (147645932445695714637/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree036.table
  base := (-1653254776558573681614703982045529388117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-95070229629208817660381496127987423250000000000)
      constant := (883980231426364841681777439577764613763546688227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree036.table
  base := (-413330970207762862288886246247447205623/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-95095045550027608504579299669305642000000000000)
      constant := (884453023680756454640058092752684668999202278852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295291864891391429273/100000000000000000000)
  centralHi := (147645932445695714637/50000000000000000000)
  directionLo := (37435076399951659981/12500000000000000000)
  directionHi := (299480611199613279849/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree037.table
  base := (-1694914752548288803401288346248322236327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-97706204311826135343121296957410083562500000000)
      constant := (934405783040712333344647247166979681251136115737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree037.table
  base := (-6779896360072611607399587466349443219741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-1172780514765345377862561807165179034000000000000)
      constant := (11218864498117340493520389194306383773357689911313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37435076399951659981/12500000000000000000)
  centralHi := (299480611199613279849/100000000000000000000)
  directionLo := (303611573392636170647/100000000000000000000)
  directionHi := (37951446674079521331/12500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree038.table
  base := (-6915551894872193638673281955046137664141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-1204106147933321436310333173441992926500000000000)
      constant := (11836023896404568548920309370856250130166744600513) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree038.table
  base := (-3457877814620817070533411542723628122539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-200736747155059908945028669716448394000000000000)
      constant := (1973724853065120934393900514081673092491695050909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303611573392636170647/100000000000000000000)
  centralHi := (37951446674079521331/12500000000000000000)
  directionLo := (307687078882767296473/100000000000000000000)
  directionHi := (153843539441383648237/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree039.table
  base := (-7021366045408719986465847274318905672137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-411912614708243082834403594465021616750000000000)
      constant := (4159065962590995417921459269310988023685918988847) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree039.table
  base := (-1755385217113394979249890734094875640463/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-103005037591281127456481852452683474500000000000)
      constant := (1040321815637716303229771228143772231272060681753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307687078882767296473/100000000000000000000)
  centralHi := (153843539441383648237/50000000000000000000)
  directionLo := (62341860583357128307/20000000000000000000)
  directionHi := (4870457858074775649/1562500000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree040.table
  base := (-7097657675123882207304195308227944269241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-422456513438712353565362797782712258000000000000)
      constant := (4378789247456639531972103562566868976124965938271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree040.table
  base := (-1774451910829742840672738582563081024951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-316925104815096901321348110141428256000000000000)
      constant := (3285844726298535958361791129302648198578001869843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62341860583357128307/20000000000000000000)
  centralHi := (4870457858074775649/1562500000000000000)
  directionLo := (315680282150036406921/100000000000000000000)
  directionHi := (157840141075018203461/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree041.table
  base := (-714488998236648459074662718265561018481/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-649500618253772436444483001650604348875000000000)
      constant := (6906756891647333403155948286136512682950110000665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree041.table
  base := (-1429003718308474724964102652025517292921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-433113462475133893697667550566408118000000000000)
      constant := (4606960272643707648929219072348713359599080681755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315680282150036406921/100000000000000000000)
  centralHi := (157840141075018203461/50000000000000000000)
  directionLo := (319601926702241204401/100000000000000000000)
  directionHi := (159800963351120602201/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree042.table
  base := (-7163448914311376397981507139978245557709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-443544310899650895027281204418093540500000000000)
      constant := (4836206538438522690229092775377800494923091307179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree042.table
  base := (-7163559175471013571123432807469363989451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-443660118530138585633537620944245228000000000000)
      constant := (4838783717075864457131106631129474149586859622781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319601926702241204401/100000000000000000000)
  centralHi := (159800963351120602201/50000000000000000000)
  directionLo := (40434503862195721163/12500000000000000000)
  directionHi := (64695206179513153861/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree043.table
  base := (-3576828108578220819790864555976509743993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-227044104815060082879120203867892090875000000000)
      constant := (2536945261748501825657687675767244556787881135183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree043.table
  base := (-7153750722391025591752305102847177691023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-1362620323755429832708223073966247014000000000000)
      constant := (15229776254937527184300334625166636452666253611339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40434503862195721163/12500000000000000000)
  centralHi := (64695206179513153861/20000000000000000000)
  directionLo := (163652141430154442927/50000000000000000000)
  directionHi := (65460856572061777171/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree044.table
  base := (-1778945062044356766655102592809287649301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-348474081270442077366899708290106117250000000000)
      constant := (3988164562216966148824812735467571762380105324393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree044.table
  base := (-889482653486836155282902026208360339021/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-116188357660036992376319440424979862000000000000)
      constant := (1330095395372690882058578684122638934773130690902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163652141430154442927/50000000000000000000)
  centralHi := (65460856572061777171/20000000000000000000)
  directionLo := (331088273111808135463/100000000000000000000)
  directionHi := (41386034138976016933/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree045.table
  base := (-3525022470082007394173628504842700001547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-237588003545529353610079407185582732125000000000)
      constant := (2783595022944614895729482680591813631417262968557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree045.table
  base := (-1762528578178209499059658935481138699563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-118825021673788165360286958019439139500000000000)
      constant := (1392537260025821838009232852565738929076747693853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331088273111808135463/100000000000000000000)
  centralHi := (41386034138976016933/12500000000000000000)
  directionLo := (167414751146380033401/50000000000000000000)
  directionHi := (334829502292760066803/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree046.table
  base := (-3478318619655367866081621052373186639133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-242859952910763988975559008844428052750000000000)
      constant := (2911399882553559982792647991836980754418209706523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree046.table
  base := (-1739174163491355434423697476701409503717/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-364385057062618015032763426841695251000000000000)
      constant := (4369418863077885206909071050902577885167483455481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167414751146380033401/50000000000000000000)
  centralHi := (334829502292760066803/100000000000000000000)
  directionLo := (67705877623460604159/20000000000000000000)
  directionHi := (84632347029325755199/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree047.table
  base := (-6835713280789798477728701836007125603643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-1488791413655991746046231663019640240250000000000)
      constant := (18253139089127600209662505575583994108814876812999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree047.table
  base := (-6835764154946309970767150858032767428869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-496393398805162045312887972833430778000000000000)
      constant := (6087607705875453450917300224720493639169519481139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67705877623460604159/20000000000000000000)
  centralHi := (84632347029325755199/25000000000000000000)
  directionLo := (171094635825128769989/50000000000000000000)
  directionHi := (342189271650257539979/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree048.table
  base := (-3343701759827321244517201700840486149783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-253403851641233259706518212162118694000000000000)
      constant := (3175963996214933248762102153889689901076913406673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree048.table
  base := (-6687447070990132755356487646761038937107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-506940054860166737248758043211267888000000000000)
      constant := (6355294860980555363951872867819799290034984508917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171094635825128769989/50000000000000000000)
  centralHi := (342189271650257539979/100000000000000000000)
  directionLo := (345810422986340759341/100000000000000000000)
  directionHi := (172905211493170379671/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree049.table
  base := (-6511816996519541317881926195204731948303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-517351602012935790143995627641928029250000000000)
      constant := (6625443109235593271189662712750123964535767756793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree049.table
  base := (-3255927135387675163632697536956493743491/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-776230066372757143776942170383657497000000000000)
      constant := (9943427611730400317075602106222654523084174370063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345810422986340759341/100000000000000000000)
  centralHi := (172905211493170379671/50000000000000000000)
  directionLo := (349394046399548826489/100000000000000000000)
  directionHi := (34939404639954882649/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree050.table
  base := (-1577261221523700775401864693887683183279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-395921625557553795656216123219714002875000000000)
      constant := (5178692816807805426212841075221986917514246657547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree050.table
  base := (-3154538390530726149089694264972087092207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-264016683485088060560249091983471054000000000000)
      constant := (3454288528720145048978837280462726541491630297017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349394046399548826489/100000000000000000000)
  centralHi := (34939404639954882649/10000000000000000000)
  directionLo := (352941285021897435639/100000000000000000000)
  directionHi := (8823532125547435891/2500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree051.table
  base := (-3039581725439971104620938751784234065609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-269219699736937165802957017138654655875000000000)
      constant := (3595184426032213451461587447464610883700888222079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree051.table
  base := (-6079190737089934366492305300586349128387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-538580023025180813056368254344779218000000000000)
      constant := (7194169731752738588771662573626386622749037382597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352941285021897435639/100000000000000000000)
  centralHi := (8823532125547435891/2500000000000000000)
  directionLo := (356453225103051084751/100000000000000000000)
  directionHi := (22278326568940692797/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree052.table
  base := (-2911118250556233218522925082959078999691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-274491649102171801168436618797499976500000000000)
      constant := (3740888747316952617286977236368938468967524492221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree052.table
  base := (-582225983968222527333598435933628477717/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-823690018620278257488357487083924492000000000000)
      constant := (11228593293114823221044722026658604223584718187405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356453225103051084751/100000000000000000000)
  centralHi := (22278326568940692797/6250000000000000000)
  directionLo := (89982724973958394813/25000000000000000000)
  directionHi := (359930899895833579253/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree053.table
  base := (-1384579361152524550766459733292854413633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 37807500000000000000000000000000000000000000
      center := (574674)
      previous := (287337)
      next := (287337)
      square := (2659517551900603680066492729952500000000000)
      linear := (-149393164008939001353105849300291187500000000)
      constant := (2077024455461494488946644788056571867780753141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree053.table
  base := (-5538337402615455979594073680602583201897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (766232)
      previous := (383116)
      next := (383116)
      square := (3546023402534138240088656973270000000000000)
      linear := (-199242910336486364160949944855982000000000000)
      constant := (2770827231569820779989635474798635878079237223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89982724973958394813/25000000000000000000)
  centralHi := (359930899895833579253/100000000000000000000)
  directionLo := (363375293207013095813/100000000000000000000)
  directionHi := (181687646603506547907/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree054.table
  base := (-2613725497877339535211499229200107834967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-285035547832641071899395822115190617750000000000)
      constant := (4041241258282429834970396298978298507910518170577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree054.table
  base := (-2613734029737112628589386114246106788639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-285109995595097444431989232739145274000000000000)
      constant := (4043371796971435432623703737971951551280824480009) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363375293207013095813/100000000000000000000)
  centralHi := (181687646603506547907/50000000000000000000)
  directionLo := (366787342647944849441/100000000000000000000)
  directionHi := (183393671323972424721/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree055.table
  base := (-4889674600996112779170664923546315475839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-580614994395751414529750847548071876750000000000)
      constant := (8391777732515073079598944118653916360683241843209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree055.table
  base := (-2444844593656379776889564470344135232629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-871149970867799371199772803784191487000000000000)
      constant := (12594297051301315692203748560603716737091357137097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366787342647944849441/100000000000000000000)
  centralHi := (183393671323972424721/50000000000000000000)
  directionLo := (370167942615509409891/100000000000000000000)
  directionHi := (92541985653877352473/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree056.table
  base := (-2262509814227339382615971009540535815537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-886738339689331027891065076298643777000000000000)
      constant := (13060551196291809828654088533547360699754329762741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree056.table
  base := (-905006418933464448265353944094089474839/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-591313303300204272735718606233964768000000000000)
      constant := (8711616570919480727681099062849874233675792561045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370167942615509409891/100000000000000000000)
  centralHi := (92541985653877352473/25000000000000000000)
  directionLo := (14940717881208103841/4000000000000000000)
  directionHi := (186758973515101298013/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree057.table
  base := (-2066756180551020107580347170303598974287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-300851395928344977995834627091726579625000000000)
      constant := (4514125669715969757759728029406359124415088175497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree057.table
  base := (-1033380753341396968157145606248225023853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-150464989838802241167897169152950469500000000000)
      constant := (2258249708162892153334615646716185406087212488843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14940717881208103841/4000000000000000000)
  centralHi := (186758973515101298013/50000000000000000000)
  directionLo := (188419085927564273641/50000000000000000000)
  directionHi := (376838171855128547283/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree058.table
  base := (-3715174826304129849674888375376258471239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-612246690587159226722628457501143800500000000000)
      constant := (9355429046316047736681139021201531215303324120609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree058.table
  base := (-1857591963443431274578813819968126155511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-918609923115320484911188120484458482000000000000)
      constant := (14040516762161037904062499888409905078073931875923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188419085927564273641/50000000000000000000)
  centralHi := (376838171855128547283/100000000000000000000)
  directionLo := (4751617467711875801/1250000000000000000)
  directionHi := (380129397416950064081/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree059.table
  base := (-3270025488966033210483350098774968626813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-1868371767952885492360762982456503325250000000000)
      constant := (29065700970142063907073163154784840905331702465809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree059.table
  base := (-654006652497552709695897346838675989071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-622953271465218348543328817367476098000000000000)
      constant := (9693653336353782788772062538308685050792562435005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4751617467711875801/1250000000000000000)
  centralHi := (380129397416950064081/100000000000000000000)
  directionLo := (191696185273750118327/50000000000000000000)
  directionHi := (76678474109500047331/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree060.table
  base := (-2798079830927556042632581005768276644147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-633334488048097768184546864136525083000000000000)
      constant := (10027664951400392132272172775965509192255125619157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree060.table
  base := (-1399043234859936602376672723132558163009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-316749963760111520239599443872656604000000000000)
      constant := (5016462549311289895730270941005712507009463011479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191696185273750118327/50000000000000000000)
  centralHi := (76678474109500047331/20000000000000000000)
  directionLo := (193313903281353441673/50000000000000000000)
  directionHi := (386627806562706883347/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree061.table
  base := (-91974033418084885445075428936851151407/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-643878386778567038915506067454215724250000000000)
      constant := (10372722746529955974039412730066494149666744805425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree061.table
  base := (-2299356504162764644844829299384136401047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-1932139750725683197245206874369450954000000000000)
      constant := (31134478834381660087048486777045405514426368109171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193313903281353441673/50000000000000000000)
  centralHi := (386627806562706883347/100000000000000000000)
  directionLo := (389836391093684398527/100000000000000000000)
  directionHi := (6091193610838818727/1562500000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree062.table
  base := (-1773849392494363272867277438562814496767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-1963266856527108928939395812315719096500000000000)
      constant := (32171220663697344517884854277703530700111637979131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree062.table
  base := (-354770846408213627745050293235418251209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-654593239630232424350939028500987428000000000000)
      constant := (10729356721000126344853614249643495969885980528395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389836391093684398527/100000000000000000000)
  centralHi := (6091193610838818727/1562500000000000000)
  directionLo := (49127347722908848389/12500000000000000000)
  directionHi := (393018781783270787113/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree063.table
  base := (-1221584637810817796709581060765379678391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-664966184239505580377424474089597006750000000000)
      constant := (11080717246144012202234810271115601183678255291921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree063.table
  base := (-1221588768775532361808038286278703361249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-665139895685237116286809098878824538000000000000)
      constant := (11086516298165400431622517592058228340803846108919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49127347722908848389/12500000000000000000)
  centralHi := (393018781783270787113/100000000000000000000)
  directionLo := (198087804929950436843/50000000000000000000)
  directionHi := (396175609859900873687/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree064.table
  base := (-642564236800973673360121786294878187061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-675510082969974851108383677407287648000000000000)
      constant := (11443653712721295860751121496561683633036802626691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree064.table
  base := (-642567762342797784943368171567789939509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-2027059655220725424668037507769984944000000000000)
      constant := (34348914703979201656610182558800929874500158348937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198087804929950436843/50000000000000000000)
  centralHi := (396175609859900873687/100000000000000000000)
  directionLo := (399307481599484373131/100000000000000000000)
  directionHi := (99826870399871093283/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree065.table
  base := (-919865553904237805163389266898377117/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-514540486275333091379507160543733716937500000000)
      constant := (8859412147407227001474048392949039305181004541810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree065.table
  base := (-9199407627641986587456101467866599601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-171558301948811625039637309908624689500000000000)
      constant := (2954680609901612855438292733507543475255194507431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399307481599484373131/100000000000000000000)
  centralHi := (99826870399871093283/25000000000000000000)
  directionLo := (402414979684877928737/100000000000000000000)
  directionHi := (201207489842438964369/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree066.table
  base := (148929701777837489716870623162514889553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-174149470107728348142575521010667232625000000000)
      constant := (3046851155289526701865361804589776657574524314457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree066.table
  base := (595716240488883387233608224274627003837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-696779863850251192094419310012335868000000000000)
      constant := (12193768836735593770480557231882046578786295568453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402414979684877928737/100000000000000000000)
  centralHi := (201207489842438964369/50000000000000000000)
  directionLo := (405498664471584765481/100000000000000000000)
  directionHi := (202749332235792382741/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree067.table
  base := (250994303787924147434379060463459304217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-707141779161382663301261287360359571750000000000)
      constant := (12568218922391944948489262199871236313822613163365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree067.table
  base := (313742332383837320890500898591315934733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-530494889928941913022717035292629733500000000000)
      constant := (9431083021520501049182495032380314206829636749631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405498664471584765481/100000000000000000000)
  centralHi := (202749332235792382741/50000000000000000000)
  directionLo := (408559075167468340763/100000000000000000000)
  directionHi := (102139768791867085191/25000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree068.table
  base := (388191941702382817325979396525507570103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-2153057033675555802096661472034150639000000000000)
      constant := (38864977139102907596356516500865084245176567411105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree068.table
  base := (48523946029449352224084474384568393151/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-179468293990065143991539862692002522000000000000)
      constant := (3240436990434362189947719655474329760390766025190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408559075167468340763/100000000000000000000)
  centralHi := (102139768791867085191/25000000000000000000)
  directionLo := (411596730933513623647/100000000000000000000)
  directionHi := (12862397841672300739/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree069.table
  base := (21229441449344639611244895208898911491/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-728229576622321204763179693995740854250000000000)
      constant := (13347724947848251935994181684391747225164512747375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree069.table
  base := (2653678588771826539537672847224853438699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-728419832015265267902029521145847198000000000000)
      constant := (13354680590742505083433004497817702975192208980131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411596730933513623647/100000000000000000000)
  centralHi := (12862397841672300739/3125000000000000000)
  directionLo := (25913258244499976391/6250000000000000000)
  directionHi := (414612131911999622257/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree070.table
  base := (26508830111323247231705302884619687773/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-184693368838197618873534724328357873875000000000)
      constant := (3436604147211722998589067916311750785407910736384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree070.table
  base := (3393128896516049180616800372678026958017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-2216899464210809879513698774571052924000000000000)
      constant := (41260725633458134053800083252200866462936229874619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25913258244499976391/6250000000000000000)
  centralHi := (414612131911999622257/100000000000000000000)
  directionLo := (26100360011740584317/6250000000000000000)
  directionHi := (417605760187849349073/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree071.table
  base := (415930767479809637039640075741013059359/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 42135000000000000000000000000000000000000000
      center := (640452)
      previous := (320226)
      next := (320226)
      square := (2963929697793610687286958174345000000000000)
      linear := (-222966883777998337500029190824575125000000000)
      constant := (4210791689385427749672469198031459995412341465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree071.table
  base := (519913314664921876312787717287418002331/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7022500000000000000000000000000000000000000
      center := (106742)
      previous := (53371)
      next := (53371)
      square := (493988282965601781214493029057500000000000)
      linear := (-37170856185542285844761439292874500000000000)
      constant := (702163846020079124386221726971187089337095558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26100360011740584317/6250000000000000000)
  centralHi := (417605760187849349073/100000000000000000000)
  directionLo := (420578080688389781029/100000000000000000000)
  directionHi := (42057808068838978103/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree072.table
  base := (4952210550537488964557286894446327058673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-759861272813729016956057303948812778000000000000)
      constant := (14561676966896499905591269219456916386080082595737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree072.table
  base := (4952209563922347533709614092372331041233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-760059800180279343709639732279358528000000000000)
      constant := (14569250304007084571180036806686458714467805248377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420578080688389781029/100000000000000000000)
  centralHi := (42057808068838978103/10000000000000000000)
  directionLo := (423529542026276922767/100000000000000000000)
  directionHi := (26470596376642307673/6250000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree073.table
  base := (2885918645989149127155675210431776068573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-385202585772099143843508253633251709625000000000)
      constant := (7489122827322536330993346771675112527675368018837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree073.table
  base := (2885918225562956595786938051662240531683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1155909684352926053468264703985793457000000000000)
      constant := (22479046090920978263107101418052975732791843403281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423529542026276922767/100000000000000000000)
  centralHi := (26470596376642307673/6250000000000000000)
  directionLo := (213230288644956602817/50000000000000000000)
  directionHi := (85292115457982641127/20000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree074.table
  base := (264727462553991175776504436907564522213/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-2342847210824002675253927131752582181500000000000)
      constant := (46202319945398059156462967581895327824001775049775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree074.table
  base := (3309092923663538583940453774341130687869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-390576556145144363790689936517516374000000000000)
      constant := (7704386521056927414647075293273454485191311289861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213230288644956602817/50000000000000000000)
  centralHi := (85292115457982641127/20000000000000000000)
  directionLo := (429371604785300398253/100000000000000000000)
  directionHi := (214685802392650199127/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree075.table
  base := (7491257244346668110657348192148091649843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-791492969005136829148934913901884701750000000000)
      constant := (15829259932474388948881769152730761088875203203467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree075.table
  base := (3745628316927786730330295290447873735641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-395849884172646709758624971706434929000000000000)
      constant := (7918738616333066255492717264275005496537337883329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429371604785300398253/100000000000000000000)
  centralHi := (214685802392650199127/50000000000000000000)
  directionLo := (432263028732925949177/100000000000000000000)
  directionHi := (216131514366462974589/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree076.table
  base := (8391048390929042256811636595304775164621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-802036867735606099879894117219575343000000000000)
      constant := (16263705493323655765331518319137218670213036180949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree076.table
  base := (8391047870850597845443848714019838197501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-2406739273200894334359360041372120904000000000000)
      constant := (48816429856886692188552570139189143398687808613007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432263028732925949177/100000000000000000000)
  centralHi := (216131514366462974589/50000000000000000000)
  directionLo := (217567619961484922237/50000000000000000000)
  directionHi := (17405409596918793779/4000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree077.table
  base := (931755921161722506877361295686548851847/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1218871149699113055916279980805898976375000000000)
      constant := (25056164979698881150937771766111170432350048482145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree077.table
  base := (9317558768621572993680866094296811903391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-812793080455302803388990084168544078000000000000)
      constant := (16712771189819997452210583222677930766213228233079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217567619961484922237/50000000000000000000)
  centralHi := (17405409596918793779/4000000000000000000)
  directionLo := (218994308165919402763/50000000000000000000)
  directionHi := (437988616331838805527/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree078.table
  base := (2567697260223881277554939104672147021787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-205781166299136160335453130963739156375000000000)
      constant := (4287618350619342322968140983378783810819788102003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree078.table
  base := (1027078866360830429274055820735793174849/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-411669868255153747662430077273190594000000000000)
      constant := (8579680467921654090838434183008957825524541947405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218994308165919402763/50000000000000000000)
  centralHi := (437988616331838805527/100000000000000000000)
  directionLo := (44082352370278160929/10000000000000000000)
  directionHi := (440823523702781609291/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree079.table
  base := (562536865974110996634508946258453409317/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-208417140981753478018192931793161816687500000000)
      constant := (4400698933359619407648095195717958814403633847865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree079.table
  base := (1406342124774909628990191152419098881303/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-625414794423984140445547668693163723500000000000)
      constant := (13208934386852217224950145702154838581046768521242) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44082352370278160929/10000000000000000000)
  centralHi := (440823523702781609291/100000000000000000000)
  directionLo := (110910079023277632009/25000000000000000000)
  directionHi := (443640316093110528037/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree080.table
  base := (6128701788671692905289147268287334386023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1266318693986224774205596395735506862000000000000)
      constant := (27091615459040228981645399261586871571396790753661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree080.table
  base := (612870165189342581179963095001388626761/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-211108262155079219799150073825513852000000000000)
      constant := (4517606480765844608932176865179933750948068413045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110910079023277632009/25000000000000000000)
  centralHi := (443640316093110528037/100000000000000000000)
  directionLo := (55804917048793344467/12500000000000000000)
  directionHi := (446439336390346755737/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree081.table
  base := (13290787419428802633775482168690127462349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-854756361387952453534690133808028549250000000000)
      constant := (18525317114648416483139883425163921265521840476981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree081.table
  base := (664539359326928865199636486637206301923/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-213744926168830392783117591419973129500000000000)
      constant := (4633725288011960132140772381272170080990473524935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/12500000000000000000)
  centralHi := (446439336390346755737/100000000000000000000)
  directionLo := (112305229199854979943/25000000000000000000)
  directionHi := (449220916799419919773/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree082.table
  base := (14350888513692430711175875446426247986981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-865300260118421724265649337125719190500000000000)
      constant := (18995516154601441078914465670427175502125310759789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree082.table
  base := (14350888315447972239458540868822592298769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-2596579082190978789205021308173188884000000000000)
      constant := (57016014594207704566730560445008299991906002595883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112305229199854979943/25000000000000000000)
  centralHi := (449220916799419919773/100000000000000000000)
  directionLo := (903970758605762687/200000000000000000)
  directionHi := (451985379302881343501/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree083.table
  base := (15437706581030543115660274688015984513529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-2627532476546672984989825621330229495250000000000)
      constant := (58415022265801211499808463078627328509371672779203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree083.table
  base := (617508256491943370907489648402708448359/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-876073016785330955004210506435566738000000000000)
      constant := (19481737057187969435642082875133803713662280316775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (903970758605762687/200000000000000000)
  centralHi := (451985379302881343501/100000000000000000000)
  directionLo := (454733036095935835651/100000000000000000000)
  directionHi := (113683259023983958913/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree084.table
  base := (3310248277365947838414594977537941774333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-886388057579360265727567743761100473000000000000)
      constant := (19953790913323139343263233988313879358558575711385) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree084.table
  base := (662049649729367394919005439249036955093/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-886619672840335646940080576813403848000000000000)
      constant := (19964097726092600551061391698539784061284057267925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454733036095935835651/100000000000000000000)
  centralHi := (113683259023983958913/25000000000000000000)
  directionLo := (457464189997955849271/100000000000000000000)
  directionHi := (57183023749744481159/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree085.table
  base := (3538298546773325872945517988020448232751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-896931956309829536458526947078791114250000000000)
      constant := (20441866625976931081751147038490545517743464974595) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree085.table
  base := (17691492611677424273457781730405566454747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-2691498986686021016627851941573722874000000000000)
      constant := (61357260605998679122691606497552935131119845116729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457464189997955849271/100000000000000000000)
  centralHi := (57183023749744481159/12500000000000000000)
  directionLo := (460179134842013467563/100000000000000000000)
  directionHi := (115044783710503366891/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree086.table
  base := (9429230228171264349039460463011875868709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1361213782560448210784229225594722633250000000000)
      constant := (31403851836321062475102229079356294364439448755463) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree086.table
  base := (4714615088095186635167438545432321245153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-226928246237586257702955179392269517000000000000)
      constant := (5236676120642228396573672778416065176393656910857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460179134842013467563/100000000000000000000)
  centralHi := (115044783710503366891/25000000000000000000)
  directionLo := (462878155843848585271/100000000000000000000)
  directionHi := (57859769480481073159/12500000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree087.table
  base := (2005214441487133094449904000836329743917/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-459009876885384038960222676857086198375000000000)
      constant := (10717947353030370113747941862130909655392175959865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree087.table
  base := (5013036081607032960794166494400808615353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-229564910251337430686922696986728794500000000000)
      constant := (5361737641458396967408349026146159692105054474657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462878155843848585271/100000000000000000000)
  centralHi := (57859769480481073159/12500000000000000000)
  directionLo := (232780764975792374357/50000000000000000000)
  directionHi := (93112305990316949743/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree088.table
  base := (5318136123066986635067471904496190547933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-232140913125309337162851139257965759500000000000)
      constant := (5485461767464416535382989015178095033389933880677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree088.table
  base := (5318136104258847110959980964471234827859/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-696604722795265811012670643743564216000000000000)
      constant := (16464868837604923999540273311219675610403508044513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232780764975792374357/50000000000000000000)
  centralHi := (93112305990316949743/20000000000000000000)
  directionLo := (468229526177406402929/100000000000000000000)
  directionHi := (46822952617740640293/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree089.table
  base := (2251966059000918931665639372704240729727/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1408661326847559929073545640524330518875000000000)
      constant := (33680637471314571638412927931652122518091920907945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree089.table
  base := (22519660526021169767536836288080272151839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-939352953115359106619430928702589398000000000000)
      constant := (22465328134097581515404287536925740668736033900791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468229526177406402929/100000000000000000000)
  centralHi := (46822952617740640293/10000000000000000000)
  directionLo := (470882405912321885299/100000000000000000000)
  directionHi := (4708824059123218853/1000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree090.table
  base := (11896746312629775388791188735810368035349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-474825724981087945056661481833622160250000000000)
      constant := (11485814218971960140110248423760657255754614813981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree090.table
  base := (23793492570841404373841686327923046599699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-949899609170363798555300999080426508000000000000)
      constant := (22983459616537798416140663886662826228846613189131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470882405912321885299/100000000000000000000)
  centralHi := (4708824059123218853/1000000000000000000)
  directionLo := (236760211612527305191/50000000000000000000)
  directionHi := (473520423225054610383/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree091.table
  base := (2509404052837154644387671082956332300649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-480097674346322580422141083492467480875000000000)
      constant := (11747728720037031777358825293628853951154711998405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree091.table
  base := (12547020241048518306373529511237284537393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1440669397838052735736756604187395427000000000000)
      constant := (35261329344716770517727475425733647312701715098251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236760211612527305191/50000000000000000000)
  centralHi := (473520423225054610383/100000000000000000000)
  directionLo := (238071912573014901277/50000000000000000000)
  directionHi := (95228765029205960511/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree092.table
  base := (3302663030098098848141011214448195861921/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-728054435567335823681431027726969202250000000000)
      constant := (18018933989828189469963225851214431113680662147894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree092.table
  base := (26421304201439417139202938677840744912701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-970992921280373182427041139836100728000000000000)
      constant := (24037607973091500566789599192726363959049736406469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238071912573014901277/50000000000000000000)
  centralHi := (95228765029205960511/20000000000000000000)
  directionLo := (119688212984338804363/25000000000000000000)
  directionHi := (478752851937355217453/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree093.table
  base := (6943820928315025883941005482067678313797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-245320786538395925576550143405079061062500000000)
      constant := (6140248019084313095484619279820667994101234926693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree093.table
  base := (27775283679809802475846716224277251734693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-981539577335377874362911210213937838000000000000)
      constant := (24573624845684078982487408394666111088918796043117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119688212984338804363/25000000000000000000)
  centralHi := (478752851937355217453/100000000000000000000)
  directionLo := (120336934337407745289/25000000000000000000)
  directionHi := (481347737349630981157/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree094.table
  base := (29155978904395145904739658018849961882207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-991827044884052973037159776938006885500000000000)
      constant := (25102697709186798706403727785473876323989359212983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree094.table
  base := (14577989437979798005008846171578562029727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1488129350085573849448171920887662422000000000000)
      constant := (37673405270507242739795462271447595378353752031589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120336934337407745289/25000000000000000000)
  centralHi := (481347737349630981157/100000000000000000000)
  directionLo := (96785741773273091367/20000000000000000000)
  directionHi := (120982177216591364209/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree095.table
  base := (1528169488968832235013958723383170466209/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-751778207710891682826089235191773145062500000000)
      constant := (19237771663369947326131003546780221604190001564815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree095.table
  base := (7640847438801625755892511084116117798743/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-250658222361346814558662837742403014500000000000)
      constant := (6415885994140660486100386583893820118029108867567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96785741773273091367/20000000000000000000)
  centralHi := (120982177216591364209/25000000000000000000)
  directionLo := (60811998492090057839/12500000000000000000)
  directionHi := (486495987936720462713/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree096.table
  base := (31997516308931449165469216597523597708981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1012914842344991514499078183573388168000000000000)
      constant := (26203985601842132805370936929396014573047183777789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree096.table
  base := (499961192006077227964044678559903654013/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-253294886375097987542630355336862292000000000000)
      constant := (6554361558486146605467597165888291909832665731152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60811998492090057839/12500000000000000000)
  centralHi := (486495987936720462713/100000000000000000000)
  directionLo := (244524895098629899627/50000000000000000000)
  directionHi := (97809958039451959851/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree097.table
  base := (8364589617111175052822236103050295301783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-255864685268865196307509346722769702312500000000)
      constant := (6690891965221214313345200811918116681666512656327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree097.table
  base := (1338334338039483195700609105367846817349/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-3071178604666189926319174475175858834000000000000)
      constant := (80331930856410370762275292942938040957983047898575) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244524895098629899627/50000000000000000000)
  centralHi := (97809958039451959851/20000000000000000000)
  directionLo := (491590325683329524677/100000000000000000000)
  directionHi := (245795162841664762339/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree098.table
  base := (17472958118609229957936677623186393137883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1551003959708895083941494885313154175750000000000)
      constant := (40993663491992525219918729676414833786139215746681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree098.table
  base := (6989183244476779714171382699192895276823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1034272857610401334042261562103123388000000000000)
      constant := (27343136130847313005115850997328273857595577315435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (491590325683329524677/100000000000000000000)
  centralHi := (245795162841664762339/50000000000000000000)
  directionLo := (98823559806131281979/20000000000000000000)
  directionHi := (61764724878832051237/12500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree099.table
  base := (18230094798924202961489356501566532963959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-522273269268199663345977896763230045875000000000)
      constant := (13950304501463081669585548515442350937494199099071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree099.table
  base := (36460189585243979059103060927427754389577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1044819513665406025978131632480960498000000000000)
      constant := (27914923769830682204207550800501602046946902158513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98823559806131281979/20000000000000000000)
  centralHi := (61764724878832051237/12500000000000000000)
  directionLo := (99326481933542440639/20000000000000000000)
  directionHi := (124158102416928050799/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree100.table
  base := (593768414620308921437258504486452764231/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-263772609316717149355728749211037683250000000000)
      constant := (7119516971367766513342645509839689628226199840624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree100.table
  base := (1187536828905975487479571162969950576287/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-791524627290308038435501277144098206000000000000)
      constant := (21369504901660373297854766467494596859964911500072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99326481933542440639/20000000000000000000)
  centralHi := (124158102416928050799/25000000000000000000)
  directionLo := (249567175999677733207/50000000000000000000)
  directionHi := (99826870399871093283/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree101.table
  base := (19784441519233355749088651506377257775567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1598451503996006802230811300242762061375000000000)
      constant := (43592228463183208196970552840805629554579684622469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree101.table
  base := (19784441514684850344818091816664548061417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-532956412887707704924935886618317359000000000000)
      constant := (14538192213911606931218139636717616279608287099473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249567175999677733207/50000000000000000000)
  centralHi := (99826870399871093283/20000000000000000000)
  directionLo := (501623815582229559631/100000000000000000000)
  directionHi := (31351488473889347477/6250000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree102.table
  base := (10290825773950453185216302308202174753927/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-269044558681951784721208350869883003875000000000)
      constant := (7412715568183215107818991608364169593394077233663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree102.table
  base := (41163303088074522714296063915941051334011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1076459481830420101785741843614471828000000000000)
      constant := (29666057446512911310089277399132223566927271207859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501623815582229559631/100000000000000000000)
  centralHi := (31351488473889347477/6250000000000000000)
  directionLo := (504100985292364625049/100000000000000000000)
  directionHi := (10082019705847292501/2000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree103.table
  base := (4278443869900455802932550605636407666927/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-543361066729138204807896303398611328375000000000)
      constant := (15123098888590015083406312034198015308032128903315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree103.table
  base := (10696109673110334289634904694897973794541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-815254603414068595291208935494231703500000000000)
      constant := (22696269193620176118121314502760933501189815512287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504100985292364625049/100000000000000000000)
  centralHi := (10082019705847292501/2000000000000000000)
  directionLo := (20262641659416117933/4000000000000000000)
  directionHi := (253283020742701474163/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree104.table
  base := (44432289840759371460343917194463594823843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-3291798096566237041040255430344739894000000000000)
      constant := (92542476466080174640405499009672455149659426328401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree104.table
  base := (22216144917592674291754683492929415871189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-548776396970214742828740992185073024000000000000)
      constant := (15431644431331015235054526992915949889807318470941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20262641659416117933/4000000000000000000)
  centralHi := (253283020742701474163/50000000000000000000)
  directionLo := (63627395018730083967/12500000000000000000)
  directionHi := (509019160149840671737/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree105.table
  base := (5763357064364417530551809009669368944927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-276952482729803737769427753358150984812500000000)
      constant := (7863686351796461651659981817041080697929145400326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree105.table
  base := (46106856510181833521915276132134438278407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1108099449995434177593352054747983158000000000000)
      constant := (31470847259931571128556088514747791754242312170783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63627395018730083967/12500000000000000000)
  centralHi := (509019160149840671737/100000000000000000000)
  directionLo := (255730256526827164663/50000000000000000000)
  directionHi := (511460513053654329327/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree106.table
  base := (47808138716300981090314510915839377599141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (766232)
      previous := (383116)
      next := (383116)
      square := (3546023402534138240088656973270000000000000)
      linear := (-398132370825804279746767610092664500000000000)
      constant := (11416147217011095147362946879306509396227269781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree106.table
  base := (47808138712281589059188826721641595136471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 151230000000000000000000000000000000000000000
      center := (2298696)
      previous := (1149348)
      next := (1149348)
      square := (10638070207602414720265970919810000000000000)
      linear := (-1194709262424819013381155705011556000000000000)
      constant := (34265967372619376877198939258392411843248850933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255730256526827164663/50000000000000000000)
  centralHi := (511460513053654329327/100000000000000000000)
  directionLo := (513890267884657916363/100000000000000000000)
  directionHi := (128472566971164479091/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree107.table
  base := (3096008527535529520721716131875094623621/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-846673296285115119404722065050988916312500000000)
      constant := (24515346398620088483097613551673295116077030148388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree107.table
  base := (9907227287431149243431939991905151425581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1129192762105443561465092195503657378000000000000)
      constant := (32703849432493849216182859793493792694284089415945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513890267884657916363/100000000000000000000)
  centralHi := (128472566971164479091/25000000000000000000)
  directionLo := (516308588384915054119/100000000000000000000)
  directionHi := (12907714709622876353/2500000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree108.table
  base := (10258169936812532432171424307069419731903/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1139441627110622763270588623385675863000000000000)
      constant := (33312258403861944164891425016162240784053405858035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree108.table
  base := (51290849681165273371549329737320782887659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1139739418160448253400962265881494488000000000000)
      constant := (33329293207673759826256718519231332076901559454371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516308588384915054119/100000000000000000000)
  centralHi := (12907714709622876353/2500000000000000000)
  directionLo := (129678908619877784753/25000000000000000000)
  directionHi := (518715634479511139013/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree109.table
  base := (53072278443710910278846267930900289408181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1149985525841092034001547826703366504250000000000)
      constant := (33943347149646135725310663204657687750879690442589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree109.table
  base := (10614455688250247939342782451224886893447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-3450858222646358836010497008777994794000000000000)
      constant := (101882096326177080206365271521676246199756417688145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129678908619877784753/25000000000000000000)
  centralHi := (518715634479511139013/100000000000000000000)
  directionLo := (260555781199986028087/50000000000000000000)
  directionHi := (20844462495998882247/4000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree110.table
  base := (10976084543386089622755697343417250498781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-3481588273714683914197521090063171436500000000000)
      constant := (103741184306428360657772569311371700384452348809835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree110.table
  base := (10976084542968506924317118576991342980093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1160832730270457637272702406637168708000000000000)
      constant := (34598066135613242583573968425433933270675402578585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260555781199986028087/50000000000000000000)
  centralHi := (20844462495998882247/4000000000000000000)
  directionLo := (523496524802598985621/100000000000000000000)
  directionHi := (261748262401299492811/50000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree111.table
  base := (56715282501550470544371762686118997305263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1171073323302030575463466233338747786750000000000)
      constant := (35223401261321158679348585881558058172976506169447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree111.table
  base := (453722259998226123729848112178266574191/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1171379386325462329208572477015005818000000000000)
      constant := (35241395288305808765074633021481725307699449784875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523496524802598985621/100000000000000000000)
  centralHi := (261748262401299492811/50000000000000000000)
  directionLo := (262935335440986468691/50000000000000000000)
  directionHi := (525870670881972937383/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree112.table
  base := (11715371559149323145512358578612792048323/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1181617222032499846194425436656438428000000000000)
      constant := (35872366627155417833568909530392690770830549232935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree112.table
  base := (5857685779424249774132987020845451159523/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1772889063570700531716663821089264392000000000000)
      constant := (53836029350166517011043070112392792693501374590805) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262935335440986468691/50000000000000000000)
  centralHi := (525870670881972937383/100000000000000000000)
  directionLo := (264117073239933915791/50000000000000000000)
  directionHi := (528234146479867831583/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree113.table
  base := (60465148597985862617311701831544227211293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-3576483362288907350776153919922387207750000000000)
      constant := (109581872598871569534478165338676620721429235265551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree113.table
  base := (2418605943868374976720602654164266293453/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1192472698435471713080312617770680038000000000000)
      constant := (36545938971007243917037613640769883673407451838925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264117073239933915791/50000000000000000000)
  centralHi := (528234146479867831583/100000000000000000000)
  directionLo := (26529354709489855471/5000000000000000000)
  directionHi := (530587094189797109421/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree114.table
  base := (31190077453490094666428146319508588891203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-601352509746719193828171921645909855250000000000)
      constant := (18594086989354118052806344796082366653447832093307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree114.table
  base := (12476030981179392611678764095100888844673/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1203019354490476405016182688148517148000000000000)
      constant := (37207153500976354114134189922235943632453922148685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26529354709489855471/5000000000000000000)
  centralHi := (530587094189797109421/100000000000000000000)
  directionLo := (266464826728702973469/50000000000000000000)
  directionHi := (532929653457405946939/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree115.table
  base := (32160938360823799584355403934872638811273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-606624459111953829193651523304755175875000000000)
      constant := (18927507982196617679860852787927309077149053535137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree115.table
  base := (64321876720728442486455932905682325036641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-3640698031636443290856158275579062774000000000000)
      constant := (113622989470009281886450077238956197420995303256987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266464826728702973469/50000000000000000000)
  centralHi := (532929653457405946939/100000000000000000000)
  directionLo := (133815490169227269293/25000000000000000000)
  directionHi := (535261960676909077173/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree116.table
  base := (16572578510269835673777706601868794962499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-917844612715782696838696687445400744750000000000)
      constant := (28895862617499489671236738923076409058017253506993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree116.table
  base := (2651612561611978464585914666489300072619/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1224112666600485788887922828904191368000000000000)
      constant := (38547467938074657696850029232799605750999932815275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133815490169227269293/25000000000000000000)
  centralHi := (535261960676909077173/100000000000000000000)
  directionLo := (537584149283762945379/100000000000000000000)
  directionHi := (26879207464188147269/5000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree117.table
  base := (13657093372902470153272570427000719810741/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1234336715684846199849221453244891634250000000000)
      constant := (39206576555515683523332823029686072747294640376145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree117.table
  base := (68285466863850688795191720944024640153001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1234659322655490480823792899282028478000000000000)
      constant := (39226567845180293053774616831869322538230680017169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537584149283762945379/100000000000000000000)
  centralHi := (26879207464188147269/5000000000000000000)
  directionLo := (539896349843750368879/100000000000000000000)
  directionHi := (6748704373046879611/1250000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree118.table
  base := (70307335191306049958443788202752286187233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1244880614415315470580180656562582275500000000000)
      constant := (39891295160933256616832143261313804578891334922377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree118.table
  base := (70307335190744726244398589673216552218811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-3735617936131485518278988908979596764000000000000)
      constant := (119734888633932923117759584570121530901047066217177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (539896349843750368879/100000000000000000000)
  centralHi := (6748704373046879611/1250000000000000000)
  directionLo := (271099345069322997537/50000000000000000000)
  directionHi := (21687947605545839803/4000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree119.table
  base := (9044489877615357965220238550351216906031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-941568384859338555983354894910204687562500000000)
      constant := (30436479479683320000515717651159488632581664600434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree119.table
  base := (72355919020446695405244989250631740606267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1255752634765499864695533040037702698000000000000)
      constant := (40602653036459127682523834642580101573248903179123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271099345069322997537/50000000000000000000)
  centralHi := (21687947605545839803/4000000000000000000)
  directionLo := (2177965180994486399/400000000000000000)
  directionHi := (544491295248621599751/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree120.table
  base := (3721560917645590666617003885076322440953/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-316492102969063503010524765799490889500000000000)
      constant := (10319652247860701934988085816542578992686935005285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree120.table
  base := (74431218352507909529130102855874265174401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1266299290820504556631403110415539808000000000000)
      constant := (41299638320618399503398288109773247197620332633769) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2177965180994486399/400000000000000000)
  centralHi := (544491295248621599751/100000000000000000000)
  directionLo := (546774287631541598217/100000000000000000000)
  directionHi := (273387143815770799109/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree121.table
  base := (76533233186894725893600014189816087817557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1276512310606723282773058266515654199250000000000)
      constant := (41981204216523044842499534461624492763813885787133) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree121.table
  base := (76533233186552142601168377530038083246041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-3830537840626527745701819542380130754000000000000)
      constant := (126007756191350387233770737938190162662100027422787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546774287631541598217/100000000000000000000)
  centralHi := (273387143815770799109/50000000000000000000)
  directionLo := (109809557439858202611/20000000000000000000)
  directionHi := (8578871674988922079/1562500000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree122.table
  base := (19665490880638658747010869105070601562699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-965292157002894415128013102375008630375000000000)
      constant := (32017318736110487257717573098857934827061258308393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree122.table
  base := (78661963522264081802989453600466722580381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1287392602930513940503143251171214028000000000000)
      constant := (42711494265949851523303717653894922316614311044389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109809557439858202611/20000000000000000000)
  centralHi := (8578871674988922079/1562500000000000000)
  directionLo := (34456994461954407269/6250000000000000000)
  directionHi := (110262382278254103261/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree123.table
  base := (40408704679813012731416011414056611203783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-648800054033830912117488336575517740875000000000)
      constant := (21702135643155931251943889557237106020630829469327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree123.table
  base := (80817409359379616355168415825600213461521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1297939258985518632439013321549051138000000000000)
      constant := (43426364927113826986267324610636686490551212357049) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34456994461954407269/6250000000000000000)
  centralHi := (110262382278254103261/20000000000000000000)
  directionLo := (553566775245186005861/100000000000000000000)
  directionHi := (276783387622593002931/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree124.table
  base := (82999570697886629239063229114225485836807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1308144006798131094965935876468726123000000000000)
      constant := (44124743131013535969732015747030667039931293540383) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree124.table
  base := (16599914139535534157117001944974656980387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-3925457745121569973124650175780664744000000000000)
      constant := (132441592141816775002302267773562605869389644081045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553566775245186005861/100000000000000000000)
  centralHi := (276783387622593002931/50000000000000000000)
  directionLo := (277906245732626726711/50000000000000000000)
  directionHi := (555812491465253453423/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree125.table
  base := (1704168950743010512579854280413641557161/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-1978031858292900548545342619679625146375000000000)
      constant := (67276760773374556109195626043100683860303125265675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree125.table
  base := (17041689507394667418528429598486988159561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1319032571095528016310753462304725358000000000000)
      constant := (44873991626422527238251944569388863920701913629045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277906245732626726711/50000000000000000000)
  centralHi := (555812491465253453423/100000000000000000000)
  directionLo := (55804917048793344467/10000000000000000000)
  directionHi := (558049170487933444671/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree126.table
  base := (87444039877262338830560932218837714899641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1329231804259069636427854283104107405500000000000)
      constant := (45583563440018166665467310249666800885646484599329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree126.table
  base := (87444039877112099310981407323223009386821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1329579227150532708246623532682562468000000000000)
      constant := (45606747664562445726538217125667453475605971732749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55804917048793344467/10000000000000000000)
  centralHi := (558049170487933444671/100000000000000000000)
  directionLo := (280138460272651947019/50000000000000000000)
  directionHi := (560276920545303894039/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree127.table
  base := (22426586929523089555781147903955148270433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-334943925747384726789703371605449511687500000000)
      constant := (11580477976079271755858322626269568384497748358177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree127.table
  base := (700830841546601381383963823407612229653/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1005094412404153050136870202295299683500000000000)
      constant := (34759099121267640558650289629473515380726915970272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280138460272651947019/50000000000000000000)
  centralHi := (560276920545303894039/100000000000000000000)
  directionLo := (140623961931543457703/25000000000000000000)
  directionHi := (562495847726173830813/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree128.table
  base := (2874855345610388587605735794609479612967/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1012739701290006133417329517304616516000000000000)
      constant := (35299664431358700303898334869085117895720015474152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree128.table
  base := (91995371059424440321498302731813593765527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1350672539260542092118363673438236688000000000000)
      constant := (47090145117804229660324674843078573108217208694063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140623961931543457703/25000000000000000000)
  centralHi := (562495847726173830813/100000000000000000000)
  directionLo := (564706056035035897023/100000000000000000000)
  directionHi := (8823532125547435891/1562500000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree129.table
  base := (94311109901492530409498606439687425561171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1360863500450477448620731893057179329250000000000)
      constant := (47816485452500431855172685968996761145394538697899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree129.table
  base := (18862221980280195542235088320814012261201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1361219195315546784054233743816073798000000000000)
      constant := (47840786532903304966265455941196543405433391514845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (564706056035035897023/100000000000000000000)
  centralHi := (8823532125547435891/1562500000000000000)
  directionLo := (566907647448950248607/100000000000000000000)
  directionHi := (17715863982779695269/3125000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree130.table
  base := (96653564243897815985051976926161537844087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1371407399180946719351691096374869970500000000000)
      constant := (48572710536382521781273022385317117808265917570703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree130.table
  base := (48326782121910103217769568700449617278311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-2057648777055827213985155721290866362000000000000)
      constant := (72896084610479540089802531476807148054938611383677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566907647448950248607/100000000000000000000)
  centralHi := (17715863982779695269/3125000000000000000)
  directionLo := (569100721972447889619/100000000000000000000)
  directionHi := (28455036098622394481/5000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree131.table
  base := (49511367043343115811022476249777816575349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-2072926946867123985123975449538840917625000000000)
      constant := (74002341740185487107070104452752538686165235471943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree131.table
  base := (49511367043310222773704116773008136310777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-691156253712778083962986942285874009000000000000)
      constant := (24679977370026260764248602361183792131285638841313) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569100721972447889619/100000000000000000000)
  centralHi := (28455036098622394481/5000000000000000000)
  directionLo := (571285377690537075979/100000000000000000000)
  directionHi := (28564268884526853799/5000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree132.table
  base := (12677327428725804373630552592394305407767/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-348123799160471315203402375752562813250000000000)
      constant := (12525759330930778427350970208619289448516939265246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree132.table
  base := (101418619429750674324493787242795171397129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1392859163480560859861843954949585128000000000000)
      constant := (50128481532101066910101893657853443235367312754801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571285377690537075979/100000000000000000000)
  centralHi := (28564268884526853799/5000000000000000000)
  directionLo := (286730855409946141493/50000000000000000000)
  directionHi := (573461710819892282987/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree133.table
  base := (103841220273216076413544939576825646401531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1403039095372354531544568706327941894250000000000)
      constant := (50877139027180289016824684270139050627415858318739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree133.table
  base := (103841220273168816010820774649164655550153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-4210217458606696655393142075982266714000000000000)
      constant := (152708910349394201172120529080838751158750863367571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286730855409946141493/50000000000000000000)
  centralHi := (573461710819892282987/100000000000000000000)
  directionLo := (575629815758301323563/100000000000000000000)
  directionHi := (143907453939575330891/25000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree134.table
  base := (13286317077110043587124454183977334544097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1060187245577117851706645932234224401625000000000)
      constant := (38742899702871018338371437242049282414766521334358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree134.table
  base := (106290536616840294986839622548464858316667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1413952475590570243733584095705259348000000000000)
      constant := (51683420493143032373695951169020228386325060236723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575629815758301323563/100000000000000000000)
  centralHi := (143907453939575330891/25000000000000000000)
  directionLo := (361118615707776573/62500000000000000)
  directionHi := (577789785132442516801/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree135.table
  base := (27191642115192691997852986674814498456373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-356031723208323268251621778240830794187500000000)
      constant := (13110804763416479169078586343450745107642090182037) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree135.table
  base := (108766568460736823892955103568388153590381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1424499131645574935669454166083096458000000000000)
      constant := (52469832662135562305276785892890075329937751734389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361118615707776573/62500000000000000)
  centralHi := (577789785132442516801/100000000000000000000)
  directionLo := (28997085492203016251/5000000000000000000)
  directionHi := (579941709844060325021/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree136.table
  base := (111269315804864149005852989759215079317723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1434670791563762343737446316281013818000000000000)
      constant := (53235197376693637384643934259021548935987362375187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree136.table
  base := (55634657902417692070625175186115042289591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-2152568681550869441407986354691400352000000000000)
      constant := (79893309935162996357531454498676214308788266502637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28997085492203016251/5000000000000000000)
  centralHi := (579941709844060325021/100000000000000000000)
  directionLo := (72760709889325573661/12500000000000000000)
  directionHi := (582085679114604589289/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree137.table
  base := (56899389324570871823846780467285212952939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-2167822035441347421702608279398056688875000000000)
      constant := (81049701859366381649986023702621869487066472110073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree137.table
  base := (56899389324558684530946925103747543907179/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-722796221877792159770597153419385339000000000000)
      constant := (27030271188531037349669580532800719331810574953251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72760709889325573661/12500000000000000000)
  centralHi := (582085679114604589289/100000000000000000000)
  directionLo := (58422178052839538603/10000000000000000000)
  directionHi := (584221780528395386031/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree138.table
  base := (11635495699358851711281859458176472267467/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-727879294512350442599682361458197550250000000000)
      constant := (27418515321158777463493719388511589496327604609615) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree138.table
  base := (116354956993567863818700261364783778887513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1456139099810589011477064377216607788000000000000)
      constant := (54864839922995582491630368338414118531505816069697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58422178052839538603/10000000000000000000)
  centralHi := (584221780528395386031/100000000000000000000)
  directionLo := (586350100074372589923/100000000000000000000)
  directionHi := (146587525018593147481/25000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree139.table
  base := (118937850838192539568015176272987980360609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1466302487755170155930323926234085741750000000000)
      constant := (55646885584913369937179766503567019191960841882921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree139.table
  base := (29734462709543760084854144884521269626391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1100014316899195277559700835695833673500000000000)
      constant := (41756324445931765095794408549368503408137790260237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586350100074372589923/100000000000000000000)
  centralHi := (146587525018593147481/25000000000000000000)
  directionLo := (294235361093243225069/50000000000000000000)
  directionHi := (588470722186486450139/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree140.table
  base := (121547460182944475041899357443554168256047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-4430539159456918279983849388655329149000000000000)
      constant := (169388098202094701794905269317448515887605182375829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree140.table
  base := (121547460182929648964017967031581221769639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1477232411920598395348804517972282008000000000000)
      constant := (56491320391802256630876546001862746557484567308991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294235361093243225069/50000000000000000000)
  centralHi := (588470722186486450139/100000000000000000000)
  directionLo := (590583729782782858547/100000000000000000000)
  directionHi := (147645932445695714637/25000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree141.table
  base := (124183785027837152061951956139456160311417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1487390285216108697392242332869467024250000000000)
      constant := (57284472089672045361090558111560146172311694849473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree141.table
  base := (124183785027824591422480895635635655188241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1487779067975603087284674588350119118000000000000)
      constant := (57313503314675191488379231353103623545391219372729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (590583729782782858547/100000000000000000000)
  centralHi := (147645932445695714637/25000000000000000000)
  directionLo := (592689204303234500607/100000000000000000000)
  directionHi := (289399025538688721/48828125000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree142.table
  base := (126846825372865203032337281832134413003373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28090000000000000000000000000000000000000000
      center := (426968)
      previous := (213484)
      next := (213484)
      square := (1975953131862407124857972116230000000000000)
      linear := (-297150205107434629661416690376345500000000000)
      constant := (11527911853170943903884549582757952659876474757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree142.table
  base := (5073873014914182487980038313427859583183/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 84270000000000000000000000000000000000000000
      center := (1280904)
      previous := (640452)
      next := (640452)
      square := (5927859395587221374573916348690000000000000)
      linear := (-891683628663325399258407850859724000000000000)
      constant := (34601258498231154278857721656038312317687078525) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592689204303234500607/100000000000000000000)
  centralHi := (289399025538688721/48828125000000000)
  directionLo := (594787225746366723813/100000000000000000000)
  directionHi := (297393612873183361907/50000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree143.table
  base := (129536581218024761413892050312152649405929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-4525434248031141716562482218514544920250000000000)
      constant := (176837682261558683267884384664550807334727425226003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree143.table
  base := (129536581218015747400898210289983785301667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1508872380085612471156414729105793338000000000000)
      constant := (58975754537359876880074490696510979608631320701723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594787225746366723813/100000000000000000000)
  centralHi := (297393612873183361907/50000000000000000000)
  directionLo := (596877872704724727089/100000000000000000000)
  directionHi := (59687787270472472709/10000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree144.table
  base := (132253052563313207506028160856016874499067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1519021981407516509585119942822538948000000000000)
      constant := (59785543395726506875125842530428738191758579062323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree144.table
  base := (132253052563305571966785668543993540811389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1519419036140617163092284799483630448000000000000)
      constant := (59815822837171536945597743753771280504797665364741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (596877872704724727089/100000000000000000000)
  centralHi := (59687787270472472709/10000000000000000000)
  directionLo := (37435076399951659981/6250000000000000000)
  directionHi := (598961222399226559697/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree145.table
  base := (67498119704364477546232071318199141614307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-764782940068992890158039573070114794625000000000)
      constant := (30315575788727771557942270597467350450425238687883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree145.table
  base := (16874529926090310941490879951726961686693/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1147474269146716391271116152396100668500000000000)
      constant := (45496389696972030883522698370668699539165587586702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37435076399951659981/6250000000000000000)
  centralHi := (598961222399226559697/100000000000000000000)
  directionLo := (601037350712444413493/100000000000000000000)
  directionHi := (300518675356222206747/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree146.table
  base := (68883070877135636221283398507404121746699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-2310164668302682576570557524186880345750000000000)
      constant := (92224077948559989175212193467954882455580124096393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree146.table
  base := (137766141754265794457779050683384993608533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1540512348250626546964024940239304668000000000000)
      constant := (61513844813733379670372041260983346399560747122077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (601037350712444413493/100000000000000000000)
  centralHi := (300518675356222206747/50000000000000000000)
  directionLo := (603106332220854791107/100000000000000000000)
  directionHi := (150776583055213697777/25000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree147.table
  base := (28112551919988026438910958935774052932859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1550653677598924321777997552775610871750000000000)
      constant := (62340244560479855490449158117426495501432082965855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree147.table
  base := (140562759599935492590256734380939398075087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1551059004305631238899895010617141778000000000000)
      constant := (62371798490483552420441204875702885189001506609703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603106332220854791107/100000000000000000000)
  centralHi := (150776583055213697777/25000000000000000000)
  directionLo := (37823015014131020553/6250000000000000000)
  directionHi := (605168240226096328849/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree148.table
  base := (143386092945736085516933028028917136188759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1561197576329393592508956756093301513000000000000)
      constant := (63203729361775139041446805365019950448803843340271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree148.table
  base := (143386092945732156163189854824387579434409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-4684816981081907792507295242984936664000000000000)
      constant := (189707141878639702678457490946569815450876467565363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37823015014131020553/6250000000000000000)
  centralHi := (605168240226096328849/100000000000000000000)
  directionLo := (121444629357054468259/20000000000000000000)
  directionHi := (37951446674079521331/6250000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree149.table
  base := (29247228358332031335280225943460406154667/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-4715224425179588589719747878232976462750000000000)
      constant := (192219519108777573820771915776036576957138685380845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree149.table
  base := (36559035447914207248938817778782316503427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-393038079103910155692908787843203999500000000000)
      constant := (16026397805230609967040466836552378643275015399163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121444629357054468259/20000000000000000000)
  centralHi := (37951446674079521331/6250000000000000000)
  directionLo := (609271122740333529239/100000000000000000000)
  directionHi := (15231778068508338231/2500000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree150.table
  base := (149112906137713754756073868389272952452719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1582285373790332133970875162728682795500000000000)
      constant := (64948575583932032139735697968815833896203215549511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree150.table
  base := (9319556633606933546546330879894269918529/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-395674743117661328676876305437663277000000000000)
      constant := (16245357568652797383502593611567544994211947485604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609271122740333529239/100000000000000000000)
  centralHi := (15231778068508338231/2500000000000000000)
  directionLo := (152828059436643687267/25000000000000000000)
  directionHi := (611312237746574749069/100000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree151.table
  base := (76008192991949299892818946761534696218649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-796414636260400702350917183023186718375000000000)
      constant := (32914968502396842997896515734543254099143949541681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree151.table
  base := (76008192991948106743859289689768773696327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-2389868442788475009965062938192735327000000000000)
      constant := (98794846680919261667794216814056729357638234997789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152828059436643687267/25000000000000000000)
  centralHi := (611312237746574749069/100000000000000000000)
  directionLo := (613346560300278275149/100000000000000000000)
  directionHi := (12266931206005565503/2000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree152.table
  base := (154946581330216660980586425373011861196757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-4810119513753812026298380708092192234000000000000)
      constant := (200151771896532542178560461529938849901151864115799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree152.table
  base := (154946581330214640346527508881098176755289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1603792284580654698579245362506327328000000000000)
      constant := (66750993758927422654739247033706870224446763883841) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613346560300278275149/100000000000000000000)
  centralHi := (12266931206005565503/2000000000000000000)
  directionLo := (615374157765534592947/100000000000000000000)
  directionHi := (153843539441383648237/25000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree153.table
  base := (157903492176670105153990362715700114647803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1613917069981739946163752772681754719250000000000)
      constant := (67610536466083547013356340427153704991630703458707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree153.table
  base := (157903492176668394224955719158354634199221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1614338940635659390515115432884164438000000000000)
      constant := (67644718189554964987965211593295073463694149028349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (615374157765534592947/100000000000000000000)
  centralHi := (153843539441383648237/25000000000000000000)
  directionLo := (617395096400270435471/100000000000000000000)
  directionHi := (38587193525016902217/6250000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree154.table
  base := (20110889815407656709046751866730408187227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-406115242178052304223677993999861340125000000000)
      constant := (17127443626627954432060971596019054996451173422726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree154.table
  base := (201108898154074756301269014671486580903/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1218664197517998061838239127446501161000000000000)
      constant := (51408303309371625827680133230327885876591191564200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617395096400270435471/100000000000000000000)
  centralHi := (38587193525016902217/6250000000000000000)
  directionLo := (309704720690756257679/50000000000000000000)
  directionHi := (619409441381512515359/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree155.table
  base := (163897460369992546586412971147023711329133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-4905014602328035462877013537951408005250000000000)
      constant := (208244914260387082267138179860565028726291026210431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree155.table
  base := (163897460369991320092041089340365290245013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1635432252745668774386855573639838658000000000000)
      constant := (69450052427749065655708003479319880709103435487197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309704720690756257679/50000000000000000000)
  centralHi := (619409441381512515359/100000000000000000000)
  directionLo := (310708628414957102939/50000000000000000000)
  directionHi := (621417256829914205879/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree156.table
  base := (166934517716866512785138290987963706138257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1645548766173147758356630382634826643000000000000)
      constant := (70326127206935211905258923186138498807159056485433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree156.table
  base := (166934517716865474407665533028394997647733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1645978908800673466322725644017675768000000000000)
      constant := (70361662235315694540816700801598625293446501746877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310708628414957102939/50000000000000000000)
  centralHi := (621417256829914205879/100000000000000000000)
  directionLo := (623418605833571283071/100000000000000000000)
  directionHi := (4870457858074775649/781250000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree157.table
  base := (169998290563885745205657485432401343413103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1656092664903617029087589585952517284250000000000)
      constant := (71243241866930407893310124808512493984517512794407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree157.table
  base := (10624893160242804133005193217605632680699/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1242394173641758618693946785796634658500000000000)
      constant := (53459425376396568411752882582100079069452450537572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623418605833571283071/100000000000000000000)
  centralHi := (4870457858074775649/781250000000000000)
  directionLo := (19544173452223492341/3125000000000000000)
  directionHi := (625413550471151754913/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree158.table
  base := (8654438945552644014229582186990728815083/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1249977422725564724863911591952655944125000000000)
      constant := (54124736550085989539190832925141465831891487935405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree158.table
  base := (10818048681940758506149619581080284301/625000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-416768055227670712548616446193337497000000000000)
      constant := (18050691806847073268770588082245858446580827476000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19544173452223492341/3125000000000000000)
  centralHi := (625413550471151754913/100000000000000000000)
  directionLo := (627402151834363768897/100000000000000000000)
  directionHi := (313701075917181884449/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree159.table
  base := (44051495689592645241777097787818714387949/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12602500000000000000000000000000000000000000
      center := (191558)
      previous := (95779)
      next := (95779)
      square := (886505850633534560022164243317500000000000)
      linear := (-149268464076589139422348521946235187500000000)
      constant := (6505459932937698833200915963680056754464025909) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree159.table
  base := (176205982758369950998797146061639668721637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50410000000000000000000000000000000000000000
      center := (766232)
      previous := (383116)
      next := (383116)
      square := (3546023402534138240088656973270000000000000)
      linear := (-597229931280059644759820525151722000000000000)
      constant := (26034981278709269448093455444510091070025772117) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627402151834363768897/100000000000000000000)
  centralHi := (313701075917181884449/50000000000000000000)
  directionLo := (629384470049784603997/100000000000000000000)
  directionHi := (314692235024892301999/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree160.table
  base := (44837475526460380674623921052855834619283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-421931090273756210320116798976397302000000000000)
      constant := (18507584771512609972710174032502689620845097938827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree160.table
  base := (179349902105840989438882286627820198590329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-5064496599062076702198617776587072624000000000000)
      constant := (222203158166140790677214423348402118180957861216803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (629384470049784603997/100000000000000000000)
  centralHi := (314692235024892301999/50000000000000000000)
  directionLo := (631360564300072813843/100000000000000000000)
  directionHi := (157840141075018203461/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree161.table
  base := (45630134238367095478736709799260659566053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1273701194869120584008569799417459886937500000000)
      constant := (56228466929101543515521654046232427107850409553871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree161.table
  base := (45630134238366982633872761698203924905909/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-424678047268924231500518998976715329500000000000)
      constant := (18752284539461527012490119007948420099505980538621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631360564300072813843/100000000000000000000)
  centralHi := (157840141075018203461/25000000000000000000)
  directionLo := (633330492844584692929/100000000000000000000)
  directionHi := (63333049284458469293/10000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree162.table
  base := (11607367956328364164210467709937907782857/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-427203039638990845685596400635242622625000000000)
      constant := (18979549566185719064723834271932482155370119191332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree162.table
  base := (185717887301253444570337693148418576946621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1709258845130701617937946066284698428000000000000)
      constant := (75956518719291909164001872715258603298303657338949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633330492844584692929/100000000000000000000)
  centralHi := (63333049284458469293/10000000000000000000)
  directionLo := (635294313039415384151/100000000000000000000)
  directionHi := (79411789129926923019/12500000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree163.table
  base := (7557678125968020350275502626798932684031/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1719356057286432653473344805858661131750000000000)
      constant := (76871066163872932157091465956685054104598501530975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree163.table
  base := (11808872071825011586755478409294198153299/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106201267500000000000000000000000000000000000000
      center := (1614259266)
      previous := (807129633)
      next := (807129633)
      square := (7470584803288795737306778078436572500000000000)
      linear := (-1289854125889279732405362102496901653500000000000)
      constant := (57682395804788278360063470040670025294967420970372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (635294313039415384151/100000000000000000000)
  centralHi := (79411789129926923019/12500000000000000000)
  directionLo := (127450416271376826391/20000000000000000000)
  directionHi := (159313020339221032989/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree164.table
  base := (38438546899462211587063065092792700464077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-5189699868050705772612912027529055319000000000000)
      constant := (233489678808576788853944213339212370387190631235195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree164.table
  base := (48048183624327696062460481003087971097573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-432588039310177750452421551760093162000000000000)
      constant := (19467291304780882814327652808977541190608749169837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127450416271376826391/20000000000000000000)
  centralHi := (159313020339221032989/25000000000000000000)
  directionLo := (639203853404482408803/100000000000000000000)
  directionHi := (159800963351120602201/25000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree165.table
  base := (97735115672794038264822370460117314248951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-870221927373685597467631606247021207125000000000)
      constant := (39397339290850452745760793654943867936759222982719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree165.table
  base := (97735115672793922451294859260254648394753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-870449406647857846872778138709104879000000000000)
      constant := (39417215578754713182588613406969921683055281193257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (639203853404482408803/100000000000000000000)
  centralHi := (159800963351120602201/25000000000000000000)
  directionLo := (641149683943302901463/100000000000000000000)
  directionHi := (80143710492912862683/12500000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree166.table
  base := (6211701365438566740259455538935540169053/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-437746938369460116416555603952933263875000000000)
      constant := (19941355775099724046402065406648115924411569899656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree166.table
  base := (99387221847016969831773055707290292631909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-2627168204026080578522139521694070302000000000000)
      constant := (119708488332313139342196440754266057364181858697863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641149683943302901463/100000000000000000000)
  centralHi := (80143710492912862683/12500000000000000000)
  directionLo := (643089626905966636153/100000000000000000000)
  directionHi := (321544813452983318077/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree167.table
  base := (202105371542651772239255768305324847425349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 424805070000000000000000000000000000000000000000
      center := (6457037064)
      previous := (3228518532)
      next := (3228518532)
      square := (29882339213155182949227112313746290000000000000)
      linear := (-5284594956624929209191544857388271090250000000000)
      constant := (242226379476858812866462489319343873324021782671943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree167.table
  base := (202105371542651606350539013488092234295509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 141601690000000000000000000000000000000000000000
      center := (2152345688)
      previous := (1076172844)
      next := (1076172844)
      square := (9960779737718394316409037437915430000000000000)
      linear := (-1761992125405725077617296418173883978000000000000)
      constant := (80782848411221566782101146732376008518712003381021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (643089626905966636153/100000000000000000000)
  centralHi := (321544813452983318077/50000000000000000000)
  directionLo := (5039247932922381609/781250000000000000)
  directionHi := (645023735414064845953/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree168.table
  base := (802589901919701118349102611454144589813/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 35400422500000000000000000000000000000000000000
      center := (538086422)
      previous := (269043211)
      next := (269043211)
      square := (2490194934429598579102259359478857500000000000)
      linear := (-443018887734694751782035205611778584500000000000)
      constant := (20431197189340766300802078269146006856475016537408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree168.table
  base := (102731507445721672958360836989636375627941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-886269390730364884776583244275860544000000000000)
      constant := (40882999863273941720503548297324095559439125682029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell170.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5039247932922381609/781250000000000000)
  centralHi := (645023735414064845953/100000000000000000000)
  directionLo := (646952061795131538609/100000000000000000000)
  directionHi := (64695206179513153861/10000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 95599
  qDenominator := 180624
  table := BinomialMassData.Q95599_180624.Degree169.table
  base := (20884737374041173946133947173615498217249/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70800845000000000000000000000000000000000000000
      center := (1076172844)
      previous := (538086422)
      next := (538086422)
      square := (4980389868859197158204518718957715000000000000)
      linear := (-891309724834624138929550012882402489625000000000)
      constant := (41356704947814656892712110086262730314701441525405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q95599_180624.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 11953
  qDenominator := 22578
  table := BinomialMassData.Q11953_22578.Degree169.table
  base := (104423686870205810335339640529219353012971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 212402535000000000000000000000000000000000000000
      center := (3228518532)
      previous := (1614259266)
      next := (1614259266)
      square := (14941169606577591474613556156873145000000000000)
      linear := (-2674628156273601692233554838394337297000000000000)
      constant := (124132669251281616607331759757573604184452985656297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11953_22578.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell170.Kernel169
