import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell059.Parameters
import ForestUnimodality.BinomialMassData.Q395_792.Batch000_049
import ForestUnimodality.BinomialMassData.Q395_792.Batch050_099
import ForestUnimodality.BinomialMassData.Q395_792.Batch100_149
import ForestUnimodality.BinomialMassData.Q1_2.Batch000_049
import ForestUnimodality.BinomialMassData.Q1_2.Batch050_099
import ForestUnimodality.BinomialMassData.Q1_2.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree000.table
  base := (5691607555993839178242410513/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-33306690738754696212708950)
      constant := (569160755599383917824241051300000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree000.table
  base := (5691607555993839178242410513/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-33306690738754696212708950)
      constant := (569160755599383917824241051300000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree001.table
  base := (326585275484998638943852822082370753143811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-32822562786094078397802764456460323041675800)
      constant := (12811634059495520275460712641844820080241711319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree001.table
  base := (325972241277117463956880071424668732941791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-839344400616137964465934824696212708950)
      constant := (326182077377271506774669239819516839296266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6249980072154742059/12500000000000000000)
  directionHi := (49999840577237936473/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree002.table
  base := (38904074345780581264588861423903601960259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-32822562786093425520050903386905161520837900)
      constant := (3829358165393221387125096848510708477116729465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree002.table
  base := (48463620382397416642738140696306369766159/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-1678688801232242622241130894696212708950)
      constant := (194693825930205804535418497609921691773586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6249980072154742059/12500000000000000000)
  centralHi := (49999840577237936473/100000000000000000000)
  directionLo := (70710452660822491221/100000000000000000000)
  directionHi := (35355226330411245611/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree003.table
  base := (15170755431517524449070015415849704809739/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-10940854262031069298044538787906702560186200)
      constant := (536855404659155892154384722471622454540366297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree003.table
  base := (120814581862414899933056441904453925130999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-2518033201848347280016326964696212708950)
      constant := (122703106763801185373086741193998244194424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70710452660822491221/100000000000000000000)
  centralHi := (35355226330411245611/50000000000000000000)
  directionLo := (86602264250120087683/100000000000000000000)
  directionHi := (21650566062530021921/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree004.table
  base := (15962581442880589323372797837853730660789/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-32822562786093099081174972852127580760418950)
      constant := (814985981134895863328298369250657270023709820) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree004.table
  base := (79397184212151365057994395250411529592589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-3357377602464451937791523034696212708950)
      constant := (82754561814615850302476657039803955010489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86602264250120087683/100000000000000000000)
  centralHi := (21650566062530021921/25000000000000000000)
  directionLo := (19999936230895174589/20000000000000000000)
  directionHi := (49999840577237936473/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree005.table
  base := (27688810865994153853877375854757454971033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-164112813930465168966998933725860323041675800)
      constant := (2375647266921697448441069019184795399327479839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree005.table
  base := (5507392924909088101306912385612353288087/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-4196722003080556595566719104696212708950)
      constant := (60319831752941618390890946180364064653245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19999936230895174589/20000000000000000000)
  centralHi := (49999840577237936473/50000000000000000000)
  directionLo := (111803042394856349999/100000000000000000000)
  directionHi := (2236060847897127/2000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree006.table
  base := (5041677026360005551166727964355536478853/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (248292)
      previous := (124146)
      next := (124146)
      square := (1828092104541875944634377040460000000000000)
      linear := (-10940854262030996756072109780178351280093100)
      constant := (104216019270562919953557828737382183938116297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree006.table
  base := (1002774563034003168970170753757812756707/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-5036066403696661253341915174696212708950)
      constant := (47665082126905168598855811044401148395130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111803042394856349999/100000000000000000000)
  centralHi := (2236060847897127/2000000000000000)
  directionLo := (122474096634738464137/100000000000000000000)
  directionHi := (61237048317369232069/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree007.table
  base := (95456790223868535863129005493945408833/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-229757939502650714251597018360560323041675800)
      constant := (1598593210959714194961450572443076726466672365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree007.table
  base := (30379197496149442931758538143558550944653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-5875410804312765911117111244696212708950)
      constant := (40661166403696841562922275642495295425978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122474096634738464137/100000000000000000000)
  centralHi := (61237048317369232069/50000000000000000000)
  directionLo := (13228714376024778641/10000000000000000000)
  directionHi := (132287143760247786411/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree008.table
  base := (11891950670536964243272999658291460742157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-65645125572185871723474015169477580760418950)
      constant := (364064727149994604784153645125974611451251264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree008.table
  base := (4730747669014595384845156616974617067773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-6714755204928870568892307314696212708950)
      constant := (37083248754930784675391875223657936174665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13228714376024778641/10000000000000000000)
  centralHi := (132287143760247786411/100000000000000000000)
  directionLo := (70710452660822491221/50000000000000000000)
  directionHi := (141420905321644982443/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree009.table
  base := (18827443896050345439749884902887761598401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4840000000000000000000000000000000000000000
      center := (55176)
      previous := (27588)
      next := (27588)
      square := (406242689898194654363194897880000000000000)
      linear := (-3646951420676990858471544481422966951131800)
      constant := (17297402227321422628460509663934573723819959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree009.table
  base := (18721583097682414494064629402225349404519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-7554099605544975226667503384696212708950)
      constant := (35718307210158683694120674215858306594794) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70710452660822491221/50000000000000000000)
  centralHi := (141420905321644982443/100000000000000000000)
  directionLo := (74999760865856904709/50000000000000000000)
  directionHi := (149999521731713809419/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree010.table
  base := (14999986805004121000035977092920703026351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-164112813930464516089247072656305161520837900)
      constant := (703275710433343189829855341799388865681256677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree010.table
  base := (2982077250275003016521831847267388814607/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-8393444006161079884442699454696212708950)
      constant := (35893996266777798060442754759818007617785) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74999760865856904709/50000000000000000000)
  centralHi := (149999521731713809419/100000000000000000000)
  directionLo := (158113378869379970769/100000000000000000000)
  directionHi := (15811337886937997077/10000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree011.table
  base := (2979324560539814633678416487922266458209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3240000000000000000000000000000000000000000
      center := (36936)
      previous := (18468)
      next := (18468)
      square := (271947585799617909119163526680000000000000)
      linear := (-2983869344190262849758621385371572917699800)
      constant := (12046124012092642044725951331179150419997489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree011.table
  base := (5919458293219057288457491039908937342771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-9232788406777184542217895524696212708950)
      constant := (37229084705075463661413726348147044584767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158113378869379970769/100000000000000000000)
  centralHi := (15811337886937997077/10000000000000000000)
  directionLo := (165830710772285185631/100000000000000000000)
  directionHi := (5182209711633912051/3125000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree012.table
  base := (4677331404013972982560509840386340677943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (124146)
      previous := (62073)
      next := (62073)
      square := (914046052270937972317188520230000000000000)
      linear := (-10940854262030960485085895276314175640046550)
      constant := (42926905324474582539717421971531516327141479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree012.table
  base := (9284379300704858051727954210253854254781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-10072132807393289199993091594696212708950)
      constant := (39500777722884825571779445258431130508481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165830710772285185631/100000000000000000000)
  centralHi := (5182209711633912051/3125000000000000000)
  directionLo := (86602264250120087683/50000000000000000000)
  directionHi := (173204528500240175367/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree013.table
  base := (3587809547219434331094652817501968977277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-426693316219207350105391272264660323041675800)
      constant := (1664564346474364012995661328684998845463018391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree013.table
  base := (7111504742726300450338659162281206645577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-10911477208009393857768287664696212708950)
      constant := (42573805668756938734830495025306589253752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86602264250120087683/50000000000000000000)
  centralHi := (173204528500240175367/100000000000000000000)
  directionLo := (180276988966256368513/100000000000000000000)
  directionHi := (90138494483128184257/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree014.table
  base := (5293514640885736650134115397116608689333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-229757939502650061373845157291005161520837900)
      constant := (905885573390679109949345288305882406470519591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree014.table
  base := (654295600495621778797377513503762878511/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-11750821608625498515543483734696212708950)
      constant := (46362240434154335608198798820903591990738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180276988966256368513/100000000000000000000)
  centralHi := (90138494483128184257/50000000000000000000)
  directionLo := (93541136416670887189/50000000000000000000)
  directionHi := (187082272833341774379/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree015.table
  base := (3650552778545033888155089841502279163549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-54704271310154766154443261877706702560186200)
      constant := (220524792444167829919486406177231134689327569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree015.table
  base := (56181206561324915829225628285089734097/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-12590166009241603173318679804696212708950)
      constant := (50808719754580931413105759807967338299333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93541136416670887189/50000000000000000000)
  centralHi := (187082272833341774379/100000000000000000000)
  directionLo := (193648549868668365831/100000000000000000000)
  directionHi := (24206068733583545729/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree016.table
  base := (2206212486854369703529580567695918453117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-131290251144371417008072099804177580760418950)
      constant := (545457929008173199298075964435778492725979217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree016.table
  base := (1077469784416411113572650298100337581649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-13429510409857707831093875874696212708950)
      constant := (55872981208263786778283759113770376834898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193648549868668365831/100000000000000000000)
  centralHi := (24206068733583545729/12500000000000000000)
  directionLo := (199999362308951745891/100000000000000000000)
  directionHi := (49999840577237936473/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree017.table
  base := (930728135381307626262700002142289595953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-557983567363578440674587441534060323041675800)
      constant := (2401929967111431964279789610622206579179404287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree017.table
  base := (441389951773777634536100763428583708779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-14268854810473812488869071944696212708950)
      constant := (61525412848061399900201396999274975443633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199999362308951745891/100000000000000000000)
  centralHi := (49999840577237936473/25000000000000000000)
  directionLo := (206154623963995911857/100000000000000000000)
  directionHi := (103077311981997955929/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree018.table
  base := (-198671292837400844384476949869172559271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (27588)
      previous := (13794)
      next := (13794)
      square := (203121344949097327181597448940000000000000)
      linear := (-3646951420676982798252385702786483475565900)
      constant := (16321760310399387508116457375427932350850293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree018.table
  base := (-60890262597035243803780114307315629053/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-15108199211089917146644268014696212708950)
      constant := (67743335399516636064792410005036651864338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206154623963995911857/100000000000000000000)
  centralHi := (103077311981997955929/50000000000000000000)
  directionLo := (212131357982467473663/100000000000000000000)
  directionHi := (828638117119013569/390625000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree019.table
  base := (-1199997209597533289006895473445629632423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-623628692935763985959185526168760323041675800)
      constant := (2907711206164457569027889079297528191733641333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree019.table
  base := (-621019646358070492480054898762003262871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-15947543611706021804419464084696212708950)
      constant := (74508792862887620792813353689590014209283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212131357982467473663/100000000000000000000)
  centralHi := (828638117119013569/390625000000000000)
  directionLo := (217944252269324542567/100000000000000000000)
  directionHi := (27243031533665567821/12500000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree020.table
  base := (-2087877377703867425641451139325644122693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-164112813930464189650371142121527580760418950)
      constant := (798028651984425959190235027525395356912210282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree020.table
  base := (-1063624210986471697020461767677011547753/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-16786888012322126462194660154696212708950)
      constant := (81807191639637855450386071011608103993994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217944252269324542567/100000000000000000000)
  centralHi := (27243031533665567821/12500000000000000000)
  directionLo := (111803042394856349999/50000000000000000000)
  directionHi := (223606084789712699999/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree021.table
  base := (-2874436888609910822288455629975351914751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-76585979834216614582642623422606702560186200)
      constant := (388540002613232918757570552003564706373416019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree021.table
  base := (-2911291796507298413082726057677756615783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-17626232412938231119969856224696212708950)
      constant := (89626428371418589826885397584132476828192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111803042394856349999/50000000000000000000)
  centralHi := (223606084789712699999/100000000000000000000)
  directionLo := (114564027090458672641/50000000000000000000)
  directionHi := (229128054180917345283/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree022.table
  base := (-892471439336436984731941922912634167829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (18468)
      previous := (9234)
      next := (9234)
      square := (135973792899808954559581763340000000000000)
      linear := (-2983869344190257454074721707110786458849900)
      constant := (15791517270576014190208360623143881149405433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree022.table
  base := (-720872998684381110185147152317893240241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-18465576813554335777745052294696212708950)
      constant := (97956307481127124413471115010068873597245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114564027090458672641/50000000000000000000)
  centralHi := (229128054180917345283/100000000000000000000)
  directionLo := (11726002011606791019/5000000000000000000)
  directionHi := (234520040232135820381/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree023.table
  base := (-836585360966942442441664507359625359147/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-754918944080135076528381695438160323041675800)
      constant := (4165834890427122968347420162339022688910137185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree023.table
  base := (-4215160697854604167724086048186573303313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-19304921214170440435520248364696212708950)
      constant := (106788136283625619849989089888319872849612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11726002011606791019/5000000000000000000)
  centralHi := (234520040232135820381/100000000000000000000)
  directionLo := (239790811600928139233/100000000000000000000)
  directionHi := (119895405800464069617/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree024.table
  base := (-472104940034201932107110705942614823589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (124146)
      previous := (62073)
      next := (62073)
      square := (914046052270937972317188520230000000000000)
      linear := (-21881708524061884699185576048764175640046550)
      constant := (125817487309155704341442310901500057232279040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree024.table
  base := (-4751160694177841237265587921859958530471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-20144265614786545093295444434696212708950)
      constant := (116114432994541629162651511214494593976929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239790811600928139233/100000000000000000000)
  centralHi := (119895405800464069617/50000000000000000000)
  directionLo := (122474096634738464137/50000000000000000000)
  directionHi := (9797927730779077131/4000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree025.table
  base := (-2595373973737299539541126630996679862399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-820564069652320621812979780072860323041675800)
      constant := (4912076530987836521452885722121364175142641083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree025.table
  base := (-5218853320010969676339623547565744143413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-20983610015402649751070640504696212708950)
      constant := (125928709276255799434668996823636914718462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122474096634738464137/50000000000000000000)
  centralHi := (9797927730779077131/4000000000000000000)
  directionLo := (62499800721547420591/25000000000000000000)
  directionHi := (49999840577237936473/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree026.table
  base := (-139942222784971862890479048032960626419/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-426693316219206697227639411195105161520837900)
      constant := (2656776852950716007693298065643355068930073855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree026.table
  base := (-1124779975964352278470522830754859991649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-21822954416018754408845836574696212708950)
      constant := (136225303824300358758635125487276465258105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62499800721547420591/25000000000000000000)
  centralHi := (49999840577237936473/20000000000000000000)
  directionLo := (254950162779864568717/100000000000000000000)
  directionHi := (127475081389932284359/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree027.table
  base := (-5946841459765899289875899628950427104783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4840000000000000000000000000000000000000000
      center := (55176)
      previous := (27588)
      next := (27588)
      square := (406242689898194654363194897880000000000000)
      linear := (-10940854262030940334537998329722966951131800)
      constant := (70786003168170369511580373250554934611866653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree027.table
  base := (-5971264917849551615732956226738164288513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-22662298816634859066621032644696212708950)
      constant := (146999252094435971904121500719160707282312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254950162779864568717/100000000000000000000)
  centralHi := (127475081389932284359/50000000000000000000)
  directionLo := (5196135855007205261/2000000000000000000)
  directionHi := (259806792750360263051/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree028.table
  base := (-6242581603340929560099251284658647377369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-229757939502649734934969226756227580760418950)
      constant := (1543060656505724791044805268233881989996620556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree028.table
  base := (-3132660068495403496349426964199998381987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-23501643217250963724396228714696212708950)
      constant := (158246182383766172224909918357346981161326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5196135855007205261/2000000000000000000)
  centralHi := (259806792750360263051/100000000000000000000)
  directionLo := (13228714376024778641/5000000000000000000)
  directionHi := (264574287520495572821/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree029.table
  base := (-6488776542287408666562269451716193568487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-951854320796691712382175949342260323041675800)
      constant := (6629131204389522083898163897517885993101637027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree029.table
  base := (-52079428896321394571406172351934444249/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-24340987617867068382171424784696212708950)
      constant := (169962231617496312922824914116603278748650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13228714376024778641/5000000000000000000)
  centralHi := (264574287520495572821/100000000000000000000)
  directionLo := (269257381838877480879/100000000000000000000)
  directionHi := (3365717272985968511/1250000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree030.table
  base := (-6688853908591156367118786882504866833371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (248292)
      previous := (124146)
      next := (124146)
      square := (1828092104541875944634377040460000000000000)
      linear := (-54704271310154693612470832869978351280093100)
      constant := (394677645268738700655996502656535981689826087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree030.table
  base := (-1677128488492328957437415031338545215609/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-25180332018483173039946620854696212708950)
      constant := (182143976184654731770030536945089009771814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269257381838877480879/100000000000000000000)
  centralHi := (3365717272985968511/1250000000000000000)
  directionLo := (136930202779076718501/50000000000000000000)
  directionHi := (273860405558153437003/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree031.table
  base := (-3422929637239308831331378916038495916857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-1017499446368877257666774033976960323041675800)
      constant := (7597322458752657198093493941219741655895167469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree031.table
  base := (-1716029443707359067822960361980233920229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-26019676419099277697721816924696212708950)
      constant := (194788374473190224012905465067370361307809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136930202779076718501/50000000000000000000)
  centralHi := (273860405558153437003/100000000000000000000)
  directionLo := (27838733051312785487/10000000000000000000)
  directionHi := (278387330513127854871/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree032.table
  base := (-139250088071485258586378989743832981089/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-262580502288742507577268269073577580760418950)
      constant := (2027099856038617526532309801233616239551294550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree032.table
  base := (-6979447917537655162954360308101547195447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-26859020819715382355497012994696212708950)
      constant := (207892718640185670134547653687037856147753) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27838733051312785487/10000000000000000000)
  centralHi := (278387330513127854871/100000000000000000000)
  directionLo := (70710452660822491221/25000000000000000000)
  directionHi := (56568362128657992977/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree033.table
  base := (-1760302025039461255621806537724680983299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (4104)
      previous := (2052)
      next := (2052)
      square := (30216398422179767679907058520000000000000)
      linear := (-994623114730085218504473938119063657522200)
      constant := (7931435890027320390240657997084526968457819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree033.table
  base := (-7056919297974477875645047293758227152827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-27698365220331487013272209064696212708950)
      constant := (221454593769760564764049272216229282544848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70710452660822491221/25000000000000000000)
  centralHi := (56568362128657992977/20000000000000000000)
  directionLo := (57445443302571494987/20000000000000000000)
  directionHi := (35903402064107184367/12500000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree034.table
  base := (-7084131068845928802411128383568797069539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-557983567363577787796835580464505161520837900)
      constant := (4592020265372357392920509119381364072702559397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree034.table
  base := (-3549344383257282109684073660335906594107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-28537709620947591671047405134696212708950)
      constant := (235471843011540248091406075739163802863936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57445443302571494987/20000000000000000000)
  centralHi := (35903402064107184367/12500000000000000000)
  directionLo := (291546665155808487749/100000000000000000000)
  directionHi := (1166186660623233951/400000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree035.table
  base := (-3546602937309589168289841699724709731087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-1148789697513248348235970203246360323041675800)
      constant := (9748444199391856794634224421840138799116001129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree035.table
  base := (-7106685075406174208170709440823757465961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-29377054021563696328822601204696212708950)
      constant := (249942537613276460102571015203859964940664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291546665155808487749/100000000000000000000)
  centralHi := (1166186660623233951/400000000000000000)
  directionLo := (59160609199440238439/20000000000000000000)
  directionHi := (73950761499300298049/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree036.table
  base := (-3535081427256660695208506061348714519887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13794)
      previous := (6897)
      next := (6897)
      square := (101560672474548663590798724470000000000000)
      linear := (-3646951420676978768142806313468241737782950)
      constant := (31884187821135892777888913183168633196381221) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree036.table
  base := (-3541317400453756460677358639590565114591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-30216398422179800986597797274696212708950)
      constant := (264864950998710995718242106985350698531918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59160609199440238439/20000000000000000000)
  centralHi := (73950761499300298049/25000000000000000000)
  directionLo := (299999043463427618837/100000000000000000000)
  directionHi := (149999521731713809419/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree037.table
  base := (-7016552653231462188071306623725794465389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-1214434823085433893520568287881060323041675800)
      constant := (10930077703238291684042862865353753191473450019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree037.table
  base := (-1757021222691626205162247917549426283507/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-31055742822795905644372993344696212708950)
      constant := (280237536220095930476690530249182229981547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299999043463427618837/100000000000000000000)
  centralHi := (149999521731713809419/50000000000000000000)
  directionLo := (304137156784107427779/100000000000000000000)
  directionHi := (15206857839205371389/5000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree038.table
  base := (-693376591897700950601171823663524769203/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-623628692935763333081433665099205161520837900)
      constant := (5773596113995238814491046397479700905583980565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree038.table
  base := (-3472211186094165198285726884355436345559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-31895087223412010302148189414696212708950)
      constant := (296058906250226083887398363840517168778932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304137156784107427779/100000000000000000000)
  centralHi := (15206857839205371389/5000000000000000000)
  directionLo := (61643943480108393223/20000000000000000000)
  directionHi := (77054929350135491529/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree039.table
  base := (-426440661970014608470404637245063892771/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-142231105406402159867240708057306702560186200)
      constant := (1353530167119314823825959333295825764226993509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree039.table
  base := (-854111456440001924283004222123424569523/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-32734431624028114959923385484696212708950)
      constant := (312327816682754430205223677557088751268341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61643943480108393223/20000000000000000000)
  centralHi := (77054929350135491529/25000000000000000000)
  directionLo := (312248904325089924421/100000000000000000000)
  directionHi := (156124452162544962211/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree040.table
  base := (-267421085351279768105189515858802703349/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-328225627860928052861866353708277580760418950)
      constant := (3208442901215002417845106804432423857529360025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree040.table
  base := (-26150819361030066075776005774713202651/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-33573776024644219617698581554696212708950)
      constant := (329043150490018832328494545615597674300344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312248904325089924421/100000000000000000000)
  centralHi := (156124452162544962211/50000000000000000000)
  directionLo := (158113378869379970769/50000000000000000000)
  directionHi := (316226757738759941539/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree041.table
  base := (-6522201995183957002690466229412578410329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-1345725074229804984089764457150460323041675800)
      constant := (13503153073505879402219627863201324309663001759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree041.table
  base := (-6530579808476503963887847602084031989361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-34413120425260324275473777624696212708950)
      constant := (346203904550442161253298445286688328544114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158113378869379970769/50000000000000000000)
  centralHi := (316226757738759941539/100000000000000000000)
  directionLo := (20009699441743166679/6250000000000000000)
  directionHi := (64031038213578133373/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree042.table
  base := (-1583494886346051964117747552681399538951/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (248292)
      previous := (124146)
      next := (124146)
      square := (1828092104541875944634377040460000000000000)
      linear := (-76585979834216542040670194414878351280093100)
      constant := (788326691950187056353026083940386361530730263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree042.table
  base := (-1268340592930441436296777271706688633843/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-35252464825876428933248973694696212708950)
      constant := (363809177707050646337883094360087023718735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20009699441743166679/6250000000000000000)
  centralHi := (64031038213578133373/20000000000000000000)
  directionLo := (64807200348562130771/20000000000000000000)
  directionHi := (10126125054462832933/3125000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree043.table
  base := (-6121672677614881303045554648087244159143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-1411370199801990529374362541785160323041675800)
      constant := (14893921880986199905315085467466373111629987453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree043.table
  base := (-6128789026844973126544407732154017298963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-36091809226492533591024169764696212708950)
      constant := (381858160157950121023890858851314555943462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64807200348562130771/20000000000000000000)
  centralHi := (10126125054462832933/3125000000000000000)
  directionLo := (327870880810138426613/100000000000000000000)
  directionHi := (163935440405069213307/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree044.table
  base := (-235440489971769751091127955997384444083/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9234)
      previous := (4617)
      next := (4617)
      square := (67986896449904477279790881670000000000000)
      linear := (-2983869344190254756232771867980393229424950)
      constant := (32262910534339157764026995731015314590890550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree044.table
  base := (-117851317742559506470170468364873830889/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-36931153627108638248799365834696212708950)
      constant := (400350124011067411786882627065072988052450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327870880810138426613/100000000000000000000)
  centralHi := (163935440405069213307/50000000000000000000)
  directionLo := (331661421544570371263/100000000000000000000)
  directionHi := (5182209711633912051/1562500000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree045.table
  base := (-5627655502118531987003419517773856792773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4840000000000000000000000000000000000000000
      center := (55176)
      previous := (27588)
      next := (27588)
      square := (406242689898194654363194897880000000000000)
      linear := (-18234757103384889810604452178022966951131800)
      constant := (201899199277799569233116880335269438863267243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree045.table
  base := (-1126737590205059508668830521128633101897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-37770498027724742906574561904696212708950)
      constant := (419284414860878434855890479812521620441890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331661421544570371263/100000000000000000000)
  centralHi := (5182209711633912051/1562500000000000000)
  directionLo := (167704563592284524999/50000000000000000000)
  directionHi := (335409127184569049999/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree046.table
  base := (-13367983957756119172934848341102769389/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-754918944080134423650629834368605161520837900)
      constant := (8554829017151736894349897520742847232584860925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree046.table
  base := (-5352743660373733919961206441465463341569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-38609842428340847564349757974696212708950)
      constant := (438660444265546396097004505946547428964281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167704563592284524999/50000000000000000000)
  centralHi := (335409127184569049999/100000000000000000000)
  directionLo := (1324669601165954183/390625000000000000)
  directionHi := (339115417898484270849/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree047.table
  base := (-1009031654201703394806944664788450995119/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-1542660450946361619943558711054560323041675800)
      constant := (17882696529170672325046845530192319063548782745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree047.table
  base := (-5050262220343096735497800300420316347663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-39449186828956952222124954044696212708950)
      constant := (458477683019901483228086590092440682312662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1324669601165954183/390625000000000000)
  centralHi := (339115417898484270849/100000000000000000000)
  directionLo := (171390818536330028393/50000000000000000000)
  directionHi := (342781637072660056787/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree048.table
  base := (-4722027998503321226918828745883258538461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (124146)
      previous := (62073)
      next := (62073)
      square := (914046052270937972317188520230000000000000)
      linear := (-43763417048123733127384937593664175640046550)
      constant := (518692551934141668406812822117663396773942471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree048.table
  base := (-4726719621091752190147610010120369916281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-40288531229573056879900150114696212708950)
      constant := (478735655133785330048943056422588735098519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171390818536330028393/50000000000000000000)
  centralHi := (342781637072660056787/100000000000000000000)
  directionLo := (346409057000480350733/100000000000000000000)
  directionHi := (173204528500240175367/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree049.table
  base := (-4378233248603414924114288098945522795077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-1608305576518547165228156795689260323041675800)
      constant := (19480347179022575999022567213616486349937300167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree049.table
  base := (-547818004095199950567049144111648863531/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-41127875630189161537675346184696212708950)
      constant := (499433932437056037238948147354664020461027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346409057000480350733/100000000000000000000)
  centralHi := (173204528500240175367/50000000000000000000)
  directionLo := (34999888404066555531/10000000000000000000)
  directionHi := (349998884040665555311/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree050.table
  base := (-160566455762529041963257919281515967903/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-820564069652319968935227919003305161520837900)
      constant := (10152463635394817769757591477135254324722756725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree050.table
  base := (-502265080325428509652934585406877932089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-41967220030805266195450542254696212708950)
      constant := (520572129742462815699542535934150294267038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34999888404066555531/10000000000000000000)
  centralHi := (349998884040665555311/100000000000000000000)
  directionLo := (176776131652056228053/50000000000000000000)
  directionHi := (353552263304112456107/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree051.table
  base := (-3630161039952911073363435586491496245947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-185994522454525856723639431147106702560186200)
      constant := (2349628719801900918868081339976556044972542493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree051.table
  base := (-227112249663297212589134670815844433309/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-42806564431421370853225738324696212708950)
      constant := (542149900506010147637508928029199913145281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176776131652056228053/50000000000000000000)
  centralHi := (353552263304112456107/100000000000000000000)
  directionLo := (71414056584179468521/20000000000000000000)
  directionHi := (178535141460448671303/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree052.table
  base := (-403318240312060752515367249693429420629/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-426693316219206370788763480660327580760418950)
      constant := (5501382125397516966435786136420545172880004743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree052.table
  base := (-201867617804353923213958022164974238541/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-43645908832037475511000934394696212708950)
      constant := (564166932931617951858568422587461942616044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71414056584179468521/20000000000000000000)
  centralHi := (178535141460448671303/50000000000000000000)
  directionLo := (360553977932512737027/100000000000000000000)
  directionHi := (90138494483128184257/25000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree053.table
  base := (-1401799205535132963018033341220738626577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-1739595827662918255797352964958660323041675800)
      constant := (22881526270899485272608570137988526747329828959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree053.table
  base := (-2806658859595473115658721405897631032441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-44485253232653580168776130464696212708950)
      constant := (586622946473064905434277295751052005754734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360553977932512737027/100000000000000000000)
  centralHi := (90138494483128184257/25000000000000000000)
  directionLo := (45500541731099904807/12500000000000000000)
  directionHi := (364004333848799238457/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree054.table
  base := (-590393163731377618718794610259493229651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (27588)
      previous := (13794)
      next := (13794)
      square := (203121344949097327181597448940000000000000)
      linear := (-10940854262030932274318839551086483475565900)
      constant := (146757048286901938924483934325470126884279457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree054.table
  base := (-591094839397979571024098388030445205779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-45324597633269684826551326534696212708950)
      constant := (609517688691549276514671487854675962318534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45500541731099904807/12500000000000000000)
  centralHi := (364004333848799238457/100000000000000000000)
  directionLo := (367422289904215392411/100000000000000000000)
  directionHi := (91855572476053848103/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree055.table
  base := (-47517435288985622848510832515789832597/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3240000000000000000000000000000000000000000
      center := (36936)
      previous := (18468)
      next := (18468)
      square := (271947585799617909119163526680000000000000)
      linear := (-14919346720951271083321909500771572917699800)
      constant := (204007158579479619261995625951942329220336005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree055.table
  base := (-475817633519369147329808733824407550033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-46163942033885789484326522604696212708950)
      constant := (632850932431852586787168108756348219295993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367422289904215392411/100000000000000000000)
  centralHi := (91855572476053848103/25000000000000000000)
  directionLo := (185404371021968161647/50000000000000000000)
  directionHi := (74161748408787264659/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree056.table
  base := (-1421178589604896595325468562421381675217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-459515879005299143431062522977677580760418950)
      constant := (6403047823843550257915577829902225824085626433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree056.table
  base := (-1423536798870818068381223322291809169871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-47003286434501894142101718674696212708950)
      constant := (656622473284156166214713180689202146680729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185404371021968161647/50000000000000000000)
  centralHi := (74161748408787264659/20000000000000000000)
  directionLo := (374164545666683548757/100000000000000000000)
  directionHi := (187082272833341774379/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree057.table
  base := (-230800383888095692277151096613273390027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-207876230978587705151838792692006702560186200)
      constant := (2950734430880644835846316515049263459733220427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree057.table
  base := (-231340524575964683379763452995024405577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-47842630835117998799876914744696212708950)
      constant := (680832127302128098785070008554361964582767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374164545666683548757/100000000000000000000)
  centralHi := (187082272833341774379/50000000000000000000)
  directionLo := (37749051814807869167/10000000000000000000)
  directionHi := (377490518148078691671/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree058.table
  base := (-406933090484589904482735516489645149349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-951854320796691059504424088272705161520837900)
      constant := (13759057697467017489573422221076971996543062277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree058.table
  base := (-81782393420870549402786513682677780003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-48681975235734103457652110814696212708950)
      constant := (705479728951040630335957386187776779659535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37749051814807869167/10000000000000000000)
  centralHi := (377490518148078691671/100000000000000000000)
  directionLo := (95196860291402907083/25000000000000000000)
  directionHi := (380787441165611628333/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree059.table
  base := (127476559763620160292641190581116642743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-1936531204379474891651147218862760323041675800)
      constant := (28496701958513425477745173424963190712375044197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree059.table
  base := (125664626289276547485785787507112338901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-49521319636350208115427306884696212708950)
      constant := (730565129262455337523726958968545387252926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95196860291402907083/25000000000000000000)
  centralHi := (380787441165611628333/100000000000000000000)
  directionLo := (192028031421979735529/50000000000000000000)
  directionHi := (384056062843959471059/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree060.table
  base := (679892220060651598579514091902216473141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (124146)
      previous := (62073)
      next := (62073)
      square := (914046052270937972317188520230000000000000)
      linear := (-54704271310154657341484618366114175640046550)
      constant := (819232340790945442656231082650681845392158674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree060.table
  base := (42389601248709848255527973146684104091/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-50360664036966312773202502954696212708950)
      constant := (756088194174474548770487073211233326933956) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (192028031421979735529/50000000000000000000)
  centralHi := (384056062843959471059/100000000000000000000)
  directionLo := (193648549868668365831/50000000000000000000)
  directionHi := (387297099737336731663/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree061.table
  base := (1250192188268444216646008641822710292611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2002176329951660436935745303497460323041675800)
      constant := (30505097553605245840949216683850311547807959019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree061.table
  base := (1248674365611473028032256082254952579827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-51200008437582417430977699024696212708950)
      constant := (782048803038743846777475932217989440202802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193648549868668365831/50000000000000000000)
  centralHi := (387297099737336731663/100000000000000000000)
  directionLo := (3905112386637569809/1000000000000000000)
  directionHi := (390511238663756980901/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree062.table
  base := (1838266907526706501741953653704055847001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-1017499446368876604789022172907405161520837900)
      constant := (15767448759419952162627004419519754321457004727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree062.table
  base := (367375657051805783496381730359344175037/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-52039352838198522088752895094696212708950)
      constant := (808446847277336637546858233317379314852635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3905112386637569809/1000000000000000000)
  centralHi := (390511238663756980901/100000000000000000000)
  directionLo := (19684956920225338303/5000000000000000000)
  directionHi := (393699138404506766061/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree063.table
  base := (2444017753419819721385742391715747703141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4840000000000000000000000000000000000000000
      center := (55176)
      previous := (27588)
      next := (27588)
      square := (406242689898194654363194897880000000000000)
      linear := (-25528659944738839286670906026322966951131800)
      constant := (402243954292671870021610944821242451659677369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree063.table
  base := (2442747663056253309383929711309155059533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-52878697238814626746528091164696212708950)
      constant := (835282229174387149147580500941739855391458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19684956920225338303/5000000000000000000)
  centralHi := (393699138404506766061/100000000000000000000)
  directionLo := (39686143128074335923/10000000000000000000)
  directionHi := (396861431280743359231/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree064.table
  base := (3067355942459781399716640347776222875281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-525161004577484688715660607612377580760418950)
      constant := (8411420602384233407843751380659717944268547081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree064.table
  base := (1533097278997853933418222033488070836747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-53718041639430731404303287234696212708950)
      constant := (862554860788887943242740859897254948359894) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39686143128074335923/10000000000000000000)
  centralHi := (396861431280743359231/100000000000000000000)
  directionLo := (399998724617903491783/100000000000000000000)
  directionHi := (49999840577237936473/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree065.table
  base := (927050387424956693592016821929750312047/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2133466581096031527504941472766860323041675800)
      constant := (34726660720953827838383746403893945534397379227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree065.table
  base := (3707139825692052800690169554003256045373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-54557386040046836062078483304696212708950)
      constant := (890264662976453680043190028019130169086248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399998724617903491783/100000000000000000000)
  centralHi := (49999840577237936473/12500000000000000000)
  directionLo := (403111602107528780791/100000000000000000000)
  directionHi := (50388950263441097599/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree066.table
  base := (2183241312264933739041644400174100235459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 180000000000000000000000000000000000000000
      center := (2052)
      previous := (1026)
      next := (1026)
      square := (15108199211089883839953529260000000000000)
      linear := (-994623114730084618984040640534531828761100)
      constant := (16448435450507523502491632763282523638529399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree066.table
  base := (4365512238154080458072103094570463817327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-55396730440662940719853679374696212708950)
      constant := (918411564509093151896055002229545483212677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (403111602107528780791/100000000000000000000)
  centralHi := (50388950263441097599/12500000000000000000)
  directionLo := (101550156268789110197/25000000000000000000)
  directionHi := (406200625075156440789/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree067.table
  base := (504213439481280176080766663991641789731/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2199111706668217072789539557401560323041675800)
      constant := (36939774940964745744494952748458763454693047865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree067.table
  base := (5041247691718167061516851745329073273457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-56236074841279045377628875444696212708950)
      constant := (946995501283142735023870389585152199023282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101550156268789110197/25000000000000000000)
  centralHi := (406200625075156440789/100000000000000000000)
  directionLo := (102316583415518785561/25000000000000000000)
  directionHi := (81853266732415028449/20000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree068.table
  base := (573509855051421495853660590619339098569/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-557983567363577461357959649929727580760418950)
      constant := (9517976506061329328525160008878399807910410565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree068.table
  base := (143357212357311964518838794401163625981/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-57075419241895150035404071514696212708950)
      constant := (976016415606510595396365326355717777143540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102316583415518785561/25000000000000000000)
  centralHi := (81853266732415028449/20000000000000000000)
  directionLo := (206154623963995911857/50000000000000000000)
  directionHi := (82461849585598364743/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree069.table
  base := (6445322598869401184096355770470118372307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-251639648026711402008237515781806702560186200)
      constant := (4357898178124528151960342032456126236233146667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree069.table
  base := (1288916544790991774692315499733714081639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-57914763642511254693179267584696212708950)
      constant := (1005474255557274676871219186853187908866970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206154623963995911857/50000000000000000000)
  centralHi := (82461849585598364743/20000000000000000000)
  directionLo := (16613194755239363737/4000000000000000000)
  directionHi := (207664934440492046713/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree070.table
  base := (1793189820982978547609104380275094818411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-1148789697513247695358218342176805161520837900)
      constant := (20193652912484464713226449883370997849233040313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree070.table
  base := (3586041825875147267471667732076187874043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-58754108043127359350954463654696212708950)
      constant := (1035368974406479666043734377628519820561336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16613194755239363737/4000000000000000000)
  centralHi := (207664934440492046713/50000000000000000000)
  directionLo := (418328679440514391927/100000000000000000000)
  directionHi := (52291084930064298991/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree071.table
  base := (7917366064066641037095078523529141163193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2330401957812588163358735726670960323041675800)
      constant := (41570571021987582522812243477299082453575704497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree071.table
  base := (1979187305562845796164277907874859475729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-59593452443743464008729659724696212708950)
      constant := (1065700530098698460533369184640714989070641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418328679440514391927/100000000000000000000)
  centralHi := (52291084930064298991/12500000000000000000)
  directionLo := (210653072669373765397/50000000000000000000)
  directionHi := (84261229067749506159/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree072.table
  base := (4339552320798115284575106902049516331173/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13794)
      previous := (6897)
      next := (6897)
      square := (101560672474548663590798724470000000000000)
      linear := (-7293902841353953506176033237618241737782950)
      constant := (132008881767761017845813402581201027172531616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree072.table
  base := (8678541586097918010350269185762420599853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-60432796844359568666504855794696212708950)
      constant := (1096468884784570753527870971074826078122053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210653072669373765397/50000000000000000000)
  centralHi := (84261229067749506159/20000000000000000000)
  directionLo := (424262715964934947327/100000000000000000000)
  directionHi := (828638117119013569/195312500000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree073.table
  base := (1891588107878037586724353997380670460803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2396047083384773708643333811305660323041675800)
      constant := (43988224485628467283930566631223100425123979935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree073.table
  base := (9457426679306169206617905092833824813137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-61272141244975673324280051864696212708950)
      constant := (1127674004400112815221834833896745588689812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424262715964934947327/100000000000000000000)
  centralHi := (828638117119013569/195312500000000000)
  directionLo := (13349963286162512461/3125000000000000000)
  directionHi := (427198825157200398753/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree074.table
  base := (10253842719707819878837803437861455968153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-1214434823085433240642816426811505161520837900)
      constant := (22611305091902844445117384591905243872582295481) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree074.table
  base := (5126686922333340886761862749566849182527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-62111485645591777982055247934696212708950)
      constant := (1159315858288115190615324479252893568596204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13349963286162512461/3125000000000000000)
  centralHi := (427198825157200398753/100000000000000000000)
  directionLo := (430114891945677097783/100000000000000000000)
  directionHi := (53764361493209637223/12500000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree075.table
  base := (2213356648215100971539271305765267015911/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-273521356550773250436436877326706702560186200)
      constant := (5163781521318744749091507216357491048871082205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree075.table
  base := (11066355491016472467297849927776152956869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-62950830046207882639830444004696212708950)
      constant := (1191394418857414896464570026666384129542494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430114891945677097783/100000000000000000000)
  centralHi := (53764361493209637223/12500000000000000000)
  directionLo := (433011321250600438417/100000000000000000000)
  directionHi := (216505660625300219209/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree076.table
  base := (5948368474700421997094884188540313337473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-623628692935763006642557734564427580760418950)
      constant := (11935623505919117608290487396049461002884298371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree076.table
  base := (2379269357318960400105892559169712570481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-63790174446823987297605640074696212708950)
      constant := (1223909661276251193482160660554304645792505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433011321250600438417/100000000000000000000)
  centralHi := (216505660625300219209/50000000000000000000)
  directionLo := (87177700907729817027/20000000000000000000)
  directionHi := (27243031533665567821/6250000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree077.table
  base := (12743681199905931549957401728177385101567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3240000000000000000000000000000000000000000
      center := (36936)
      previous := (18468)
      next := (18468)
      square := (271947585799617909119163526680000000000000)
      linear := (-20887085409331775200103553558471572917699800)
      constant := (405190002408786107005646551006846474404018083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree077.table
  base := (12743325383071554817364699105631159126151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-64629518847440091955380836144696212708950)
      constant := (1256861563196293966112242515918935348420726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87177700907729817027/20000000000000000000)
  centralHi := (27243031533665567821/6250000000000000000)
  directionLo := (219373410220273227941/50000000000000000000)
  directionHi := (438746820440546455883/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree078.table
  base := (13607595606803570170028913201645660094321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (248292)
      previous := (124146)
      next := (124146)
      square := (1828092104541875944634377040460000000000000)
      linear := (-142231105406402087325268279049578351280093100)
      constant := (2796140094223569277793508714901176359982992263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree078.table
  base := (13607271167179003578323725700220680116717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-65468863248056196613156032214696212708950)
      constant := (1290250104504275487015335759603372975765767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219373410220273227941/50000000000000000000)
  centralHi := (438746820440546455883/100000000000000000000)
  directionLo := (55198329416585143523/12500000000000000000)
  directionHi := (88317327066536229637/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree079.table
  base := (14488461817947602625139355794894106161529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2592982460101330344497128065209760323041675800)
      constant := (51650087517882316642945619191086506133304428041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree079.table
  base := (14488166037185143979767162893050935387129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-66308207648672301270931228284696212708950)
      constant := (1324075267098463751887801011921051337390654) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55198329416585143523/12500000000000000000)
  centralHi := (88317327066536229637/20000000000000000000)
  directionLo := (27775518992829729777/6250000000000000000)
  directionHi := (444408303885275676433/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree080.table
  base := (3077252662393019045121022555736197479213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-656451255721855779284856776881777580760418950)
      constant := (13246671777333355845825065782542806337303730565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree080.table
  base := (3846498425430832950441848338384017973773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-67147552049288405928706424354696212708950)
      constant := (1358337034687492116509710655541384580253092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27775518992829729777/6250000000000000000)
  centralHi := (444408303885275676433/100000000000000000000)
  directionLo := (447212169579425399997/100000000000000000000)
  directionHi := (223606084789712699999/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree081.table
  base := (4075246303906747623509917131586424639897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4840000000000000000000000000000000000000000
      center := (55176)
      previous := (27588)
      next := (27588)
      square := (406242689898194654363194897880000000000000)
      linear := (-32822562786092788762737359874622966951131800)
      constant := (670868146756635743851896638603058392094585467) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree081.table
  base := (16300739498741754693232264374651263406979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-67986896449904510586481620424696212708950)
      constant := (1393035392609308768529972537757347878119454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447212169579425399997/100000000000000000000)
  centralHi := (223606084789712699999/50000000000000000000)
  directionLo := (14062455162348169633/3125000000000000000)
  directionHi := (449998565195141428257/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree082.table
  base := (8616307069718916370515601041574638257707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-1345725074229804331212012596080905161520837900)
      constant := (27855492663411376202104005976203216526916685103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree082.table
  base := (17232390232560123487003938199375719031477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-68826240850520615244256816494696212708950)
      constant := (1428170327668233418781428820811920440098427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14062455162348169633/3125000000000000000)
  centralHi := (449998565195141428257/100000000000000000000)
  directionLo := (7074497082380633757/1562500000000000000)
  directionHi := (452767813272360560449/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree083.table
  base := (9090569014813380466261889375499499716083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2724272711245701435066324234479160323041675800)
      constant := (57098682955383162003934286942943308165053460489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree083.table
  base := (909046701361119184467729159762550448403/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-69665585251136719902032012564696212708950)
      constant := (1463741827988310012770351673072643836389485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7074497082380633757/1562500000000000000)
  centralHi := (452767813272360560449/100000000000000000000)
  directionLo := (14235007079585317519/3125000000000000000)
  directionHi := (455520226546730160609/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree084.table
  base := (2393318254362925728320426305749139371887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (124146)
      previous := (62073)
      next := (62073)
      square := (914046052270937972317188520230000000000000)
      linear := (-76585979834216505769683979911014175640046550)
      constant := (1625094787432076011539469126378251966521950919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree084.table
  base := (19146360194515483649015340607439169204133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-70504929651752824559807208634696212708950)
      constant := (1499749882881325498845472235784680102980033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14235007079585317519/3125000000000000000)
  centralHi := (455520226546730160609/100000000000000000000)
  directionLo := (114564027090458672641/25000000000000000000)
  directionHi := (91651221672366938113/20000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree085.table
  base := (20128828386505642485705623177230240708377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2789917836817886980350922319113860323041675800)
      constant := (59925173120362925292620243614088423146029526283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree085.table
  base := (20128659115187319377055735854828931961951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-71344274052368929217582404704696212708950)
      constant := (1536194482728027773017860034366917972092326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114564027090458672641/25000000000000000000)
  centralHi := (91651221672366938113/20000000000000000000)
  directionLo := (230487876529701008193/50000000000000000000)
  directionHi := (460975753059402016387/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree086.table
  base := (211279762902131506891266702026222245977/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-1411370199801989876496610680715605161520837900)
      constant := (30681982464519557600797588984540270653209145025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree086.table
  base := (5281955533010932374297968557020967076869/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-72183618452985033875357600774696212708950)
      constant := (1573075618871222673911231174110021014792326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230487876529701008193/50000000000000000000)
  centralHi := (460975753059402016387/100000000000000000000)
  directionLo := (46367944634891031229/10000000000000000000)
  directionHi := (463679446348910312291/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree087.table
  base := (691999432160408038815377442661981169339/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-317284773598896947292835600416506702560186200)
      constant := (6979976384801048660179924591234017677743369013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree087.table
  base := (22143841453736475749480272691971839365457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-73022962853601138533132796844696212708950)
      constant := (1610393283519561963265642171978757092204782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46367944634891031229/10000000000000000000)
  centralHi := (463679446348910312291/100000000000000000000)
  directionLo := (466367465657909295373/100000000000000000000)
  directionHi := (233183732828954647687/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree088.table
  base := (2897104734522880526456273746941066903353/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 810000000000000000000000000000000000000000
      center := (9234)
      previous := (4617)
      next := (4617)
      square := (67986896449904477279790881670000000000000)
      linear := (-5967738688380506814623593896830393229424950)
      constant := (132836033974098674215804208482712847533689994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree088.table
  base := (23176710068172988052831945997113913943107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-73862307254217243190907992914696212708950)
      constant := (1648147469660953071000004042723747273136907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466367465657909295373/100000000000000000000)
  centralHi := (233183732828954647687/50000000000000000000)
  directionLo := (11726002011606791019/2500000000000000000)
  directionHi := (469040080464271640761/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree089.table
  base := (12113269007652263338702020141512514177871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2921208087962258070920118488383260323041675800)
      constant := (65782523618266915574865682093054917796923803243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree089.table
  base := (4845284332917120644955978865066091706271/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-74701651654833347848683188984696212708950)
      constant := (1686338170984628333931849786526811924079630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11726002011606791019/2500000000000000000)
  centralHi := (469040080464271640761/100000000000000000000)
  directionLo := (235848776305750431451/50000000000000000000)
  directionHi := (471697552611500862903/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree090.table
  base := (5058615294107004218728380046640169023617/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (27588)
      previous := (13794)
      next := (13794)
      square := (203121344949097327181597448940000000000000)
      linear := (-18234757103384881750385293399386483475565900)
      constant := (415366893587518990740386260897290965069545945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree090.table
  base := (6323242640848568671433253708841222310339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-75540996055449452506458385054696212708950)
      constant := (1724965381811007705481588300546694461144106) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235848776305750431451/50000000000000000000)
  centralHi := (471697552611500862903/100000000000000000000)
  directionLo := (118585034152034978077/25000000000000000000)
  directionHi := (474340136608139912309/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree091.table
  base := (527528960843114201975267866548316130391/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-2986853213534443616204716573017960323041675800)
      constant := (68813379668347464579835732262298984262041221825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree091.table
  base := (26376351653083348733153037714499027598539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-76380340456065557164233581124696212708950)
      constant := (1764029097028575531946681314970676705855764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118585034152034978077/25000000000000000000)
  centralHi := (474340136608139912309/100000000000000000000)
  directionLo := (476968079912249518929/100000000000000000000)
  directionHi := (47696807991224951893/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree092.table
  base := (27476648049208423761770072404057231179927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-754918944080134097211753903833827580760418950)
      constant := (17588588039065698930142573240336149499604596652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree092.table
  base := (13738280166695477768078404452169780846131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-77219684856681661822008777194696212708950)
      constant := (1803529312037069943496245675740365346303962) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476968079912249518929/100000000000000000000)
  centralHi := (47696807991224951893/10000000000000000000)
  directionLo := (479581623201856278467/100000000000000000000)
  directionHi := (119895405800464069617/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree093.table
  base := (1787104517359166668551054830741870908457/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-339166482122958795721034961961406702560186200)
      constant := (7990261562191167946337731847060454366083849447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree093.table
  base := (28593592464179717402661757806167336322009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-78059029257297766479783973264696212708950)
      constant := (1843466022696353562438198812257041227288184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479581623201856278467/100000000000000000000)
  centralHi := (119895405800464069617/25000000000000000000)
  directionLo := (3767039067439117627/781250000000000000)
  directionHi := (482181000632207056257/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree094.table
  base := (7431879233562176114926343127446891305071/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-1542660450946360967065806849985005161520837900)
      constant := (36743692614999692946046628892148866456060016093) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree094.table
  base := (14863722159710306823053289958241126221897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-78898373657913871137559169334696212708950)
      constant := (1883839225280397368085979420017204249764444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3767039067439117627/781250000000000000)
  centralHi := (482181000632207056257/100000000000000000000)
  directionLo := (96953288016121592667/20000000000000000000)
  directionHi := (60595805010075995417/12500000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree095.table
  base := (7719544650919445625629721354375389216167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-3118143464678814706773912742287360323041675800)
      constant := (75079445533216317920434781209414871814538207397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree095.table
  base := (30878112545778662830126231113178103402561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-79737718058529975795334365404696212708950)
      constant := (1924648916435866379003222454898748207077686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96953288016121592667/20000000000000000000)
  centralHi := (60595805010075995417/12500000000000000000)
  directionLo := (487338163379572480731/100000000000000000000)
  directionHi := (121834540844893120183/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree096.table
  base := (32045654211725917944489756341015882435649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (124146)
      previous := (62073)
      next := (62073)
      square := (914046052270937972317188520230000000000000)
      linear := (-87526834096247429983783660683464175640046550)
      constant := (2130237079134614928922403932473226826617074761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree096.table
  base := (32045594125340221235234428208108110183337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-80577062459146080453109561474696212708950)
      constant := (1965895093144846951470441633713526320212937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487338163379572480731/100000000000000000000)
  centralHi := (121834540844893120183/25000000000000000000)
  directionLo := (122474096634738464137/25000000000000000000)
  directionHi := (489896386538953856549/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree097.table
  base := (33229940990823946688381036931066565852731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-3183788590251000252058510826922060323041675800)
      constant := (78314653068389062945140461540077069824889718999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree097.table
  base := (3322988634206771971449822298680239905561/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-81416406859762185110884757544696212708950)
      constant := (2007577752691301516340704008247068715439685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122474096634738464137/25000000000000000000)
  centralHi := (489896386538953856549/100000000000000000000)
  directionLo := (98488263991538260567/20000000000000000000)
  directionHi := (123110329989422825709/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree098.table
  base := (34431036449542137388995431553897428919503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-1608305576518546512350404934619705161520837900)
      constant := (39978900047085541622289713172255903402275596681) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree098.table
  base := (17215493375804540694074238976377121432483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-82255751260378289768659953614696212708950)
      constant := (2049696892630877996734240441002868665603516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98488263991538260567/20000000000000000000)
  centralHi := (123110329989422825709/25000000000000000000)
  directionLo := (123743292156439359637/25000000000000000000)
  directionHi := (494973168625757438549/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree099.table
  base := (35648938345043159808601214342033901740393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (456)
      previous := (228)
      next := (228)
      square := (3357377602464418631100784280000000000000)
      linear := (-331541038243361473047965402668784850835800)
      constant := (8327515135013162294141761187780012616979197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree099.table
  base := (1114027911066448135801869461769392321493/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-83095095660994394426435149684696212708950)
      constant := (2092252510763738426740525561651583083380801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123743292156439359637/25000000000000000000)
  centralHi := (494973168625757438549/100000000000000000000)
  directionLo := (248746066158427778447/50000000000000000000)
  directionHi := (99498426463371111379/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree100.table
  base := (7376728931656586510969819326294569743133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-820564069652319642496351988468527580760418950)
      constant := (20823795055378304994786681299513445365055854540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree100.table
  base := (7376720713968306212686596903775177552127/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-83934440061610499084210345754696212708950)
      constant := (2135244605110104840835960097253686523208135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248746066158427778447/50000000000000000000)
  centralHi := (99498426463371111379/20000000000000000000)
  directionLo := (499998405772379364729/100000000000000000000)
  directionHi := (49999840577237936473/10000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree101.table
  base := (762703071433704942096031298584780542223/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-3315078841395371342627706996191460323041675800)
      constant := (84989413172662474568436155455398838792031756975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree101.table
  base := (19067558108514056260833169988632275603293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-84773784462226603741985541824696212708950)
      constant := (2178673173888250698000742424606923293008561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499998405772379364729/100000000000000000000)
  centralHi := (49999840577237936473/10000000000000000000)
  directionLo := (251246089438557299757/50000000000000000000)
  directionHi := (100498435775422919903/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree102.table
  base := (39403463449043407156192900008362695713893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (248292)
      previous := (124146)
      next := (124146)
      square := (1828092104541875944634377040460000000000000)
      linear := (-185994522454525784181667002139378351280093100)
      constant := (4816704145975884449495425939827386328884746579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree102.table
  base := (492542868652542070183430746000353817927/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-85613128862842708399760737894696212708950)
      constant := (2222538215494693279129187114239535153590610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251246089438557299757/50000000000000000000)
  centralHi := (100498435775422919903/20000000000000000000)
  directionLo := (252486818413565574877/50000000000000000000)
  directionHi := (100994727365426229951/20000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree103.table
  base := (40688572817426736983825579939791301697673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-3380723966967556887912305080826160323041675800)
      constant := (88428964528478782335460615932829550562905294417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree103.table
  base := (40688541952301659416223523949157558054363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-86452473263458813057535933964696212708950)
      constant := (2266839728486366953295060346473512512565288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252486818413565574877/50000000000000000000)
  centralHi := (100994727365426229951/20000000000000000000)
  directionLo := (507442960290285783199/100000000000000000000)
  directionHi := (634303700362857229/125000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree104.table
  base := (8398096070178394344013766178332299396497/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-853386632438412415138651030785877580760418950)
      constant := (22543570705854695386548601411476064505710702235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree104.table
  base := (41990452298630492991181814294942764008699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-87291817664074917715311130034696212708950)
      constant := (2311577711564579219563230402819145824874099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507442960290285783199/100000000000000000000)
  centralHi := (634303700362857229/125000000000000000)
  directionLo := (101980065111945827487/20000000000000000000)
  directionHi := (127475081389932284359/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree105.table
  base := (5413648106977436409535634340719523049651/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-382929899171082492577433685051206702560186200)
      constant := (10215181051732361570796009826976268135804594923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree105.table
  base := (10827289840607757337997384844382985948687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-88131162064691022373086326104696212708950)
      constant := (2356752163560571240946137491936583111014623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101980065111945827487/20000000000000000000)
  centralHi := (127475081389932284359/25000000000000000000)
  directionLo := (512345904700786080907/100000000000000000000)
  directionHi := (128086476175196520227/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree106.table
  base := (22322342628856159243892466297721183824377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-1739595827662917602919601103889105161520837900)
      constant := (46858002206435810307802590957586308087213354283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree106.table
  base := (44644662091882666989081909190235509148901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-88970506465307127030861522174696212708950)
      constant := (2402363083422522415934216823819134782723251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512345904700786080907/100000000000000000000)
  centralHi := (128086476175196520227/25000000000000000000)
  directionLo := (257389932845777877571/50000000000000000000)
  directionHi := (514779865691555755143/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree107.table
  base := (5749622573663996188533054679673883229969/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-3512014218111927978481501250095560323041675800)
      constant := (95512407627339479380807185338312117512298339033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree107.table
  base := (9199391908081448056817795575412174002353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-89809850865923231688636718244696212708950)
      constant := (2448410470203854578909098452610808249940590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257389932845777877571/50000000000000000000)
  centralHi := (514779865691555755143/100000000000000000000)
  directionLo := (129300593139389105261/25000000000000000000)
  directionHi := (103440474511511284209/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree108.table
  base := (11841517494974949801225955146622521204037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1210000000000000000000000000000000000000000
      center := (13794)
      previous := (6897)
      next := (6897)
      square := (101560672474548663590798724470000000000000)
      linear := (-10940854262030928244209260161768241737782950)
      constant := (300388392206355483546243927473635366593335533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree108.table
  base := (11841512714035720338040838506995050765359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-90649195266539336346411914314696212708950)
      constant := (2494894323052705861985934986901575689344736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129300593139389105261/25000000000000000000)
  centralHi := (103440474511511284209/20000000000000000000)
  directionLo := (5196135855007205261/1000000000000000000)
  directionHi := (519613585500720526101/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree109.table
  base := (48751952645665587187988686900008301579463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-3577659343684113523766099334730260323041675800)
      constant := (99156298724702216599974360257434209020221458827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree109.table
  base := (48751935272470572929823043682397819593197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-91488539667155441004187110384696212708950)
      constant := (2541814641202457247901244432730841412230972) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5196135855007205261/1000000000000000000)
  centralHi := (519613585500720526101/100000000000000000000)
  directionLo := (65251707627878383581/12500000000000000000)
  directionHi := (522013661023027068649/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree110.table
  base := (10030925576207381195026683867669471685151/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (18468)
      previous := (9234)
      next := (9234)
      square := (135973792899808954559581763340000000000000)
      linear := (-14919346720951265687638009822510786458849900)
      constant := (417371018798377428622982325933143612515765435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree110.table
  base := (3134663256218007453250871254385261392231/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-92327884067771545661962306454696212708950)
      constant := (2589171423963206540889972683328455881267946) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65251707627878383581/12500000000000000000)
  centralHi := (522013661023027068649/100000000000000000000)
  directionLo := (65550344005630156747/12500000000000000000)
  directionHi := (524402752045041253977/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree111.table
  base := (51574095050873432018052598242517203660227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-404811607695144341005633046596106702560186200)
      constant := (11429811391497166533884237640478494268375468937) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree111.table
  base := (2578704035816839471357886263840456149113/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-93167228468387650319737502524696212708950)
      constant := (2636964670714095010060541420779948928328985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65550344005630156747/12500000000000000000)
  centralHi := (524402752045041253977/100000000000000000000)
  directionLo := (65847626002451939709/12500000000000000000)
  directionHi := (526781008019615517673/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree112.table
  base := (3313147098964995017568709249802931152957/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-919031758010597960423249115420577580760418950)
      constant := (26187461656272347822046526952813632023450961412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree112.table
  base := (2650517028214768130139510912098878605757/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-94006572869003754977512698594696212708950)
      constant := (2685194380896401434560486464024965483816340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65847626002451939709/12500000000000000000)
  centralHi := (526781008019615517673/100000000000000000000)
  directionLo := (13228714376024778641/2500000000000000000)
  directionHi := (529148575040991145641/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree113.table
  base := (3403962685255010588661686108087895927561/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-3708949594828484614335295503999660323041675800)
      constant := (106648418833875433458889328987721845312172793979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree113.table
  base := (54463391140564831498896969953117746229167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-94845917269619859635287894664696212708950)
      constant := (2733860554007326807109793364050953764284842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13228714376024778641/2500000000000000000)
  centralHi := (529148575040991145641/100000000000000000000)
  directionLo := (106301119189905173241/20000000000000000000)
  directionHi := (265752797974762933103/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree114.table
  base := (13983310682380513118720425654815897038003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21780000000000000000000000000000000000000000
      center := (248292)
      previous := (124146)
      next := (124146)
      square := (1828092104541875944634377040460000000000000)
      linear := (-207876230978587632609866363684278351280093100)
      constant := (6031334396203916936216618632977143605276133011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree114.table
  base := (55933231992674695424120630788194723089669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-95685261670235964293063090734696212708950)
      constant := (2782963189594400627017104771235878847499819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106301119189905173241/20000000000000000000)
  centralHi := (265752797974762933103/50000000000000000000)
  directionLo := (533852210432259853293/100000000000000000000)
  directionHi := (266926105216129926647/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree115.table
  base := (11483974492550132612233486710908676302691/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-3774594720400670159619893588634360323041675800)
      constant := (110496647502125953077148381071312788487904150445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree115.table
  base := (57419862713448680958658487400183911933547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-96524606070852068950838286804696212708950)
      constant := (2832502287250446620862617972232716142698172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533852210432259853293/100000000000000000000)
  centralHi := (266926105216129926647/50000000000000000000)
  directionLo := (10723771102390409851/2000000000000000000)
  directionHi := (536188555119520492551/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree116.table
  base := (7365411473549113279645991416086507513101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-951854320796690733065548157737927580760418950)
      constant := (28111575982631412830149619084760181651847824583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree116.table
  base := (11784656587294788967147557053014448983299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-97363950471468173608613482874696212708950)
      constant := (2882477846609051945379560212517452582035595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10723771102390409851/2000000000000000000)
  centralHi := (536188555119520492551/100000000000000000000)
  directionLo := (269257381838877480879/50000000000000000000)
  directionHi := (538514763677754961759/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree117.table
  base := (30221750184281258123219168468695854012937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4840000000000000000000000000000000000000000
      center := (55176)
      previous := (27588)
      next := (27588)
      square := (406242689898194654363194897880000000000000)
      linear := (-47410368468800687714870267571222966951131800)
      constant := (1412506029674359338512762431411939749117043391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree117.table
  base := (30221746166011704127331343960632812425733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-98203294872084278266388678944696212708950)
      constant := (2932889867340489521767235655628494068325041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269257381838877480879/50000000000000000000)
  centralHi := (538514763677754961759/100000000000000000000)
  directionLo := (540830966898769105541/100000000000000000000)
  directionHi := (270415483449384552771/50000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree118.table
  base := (12396099579823914459733995251684032927303/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-1936531204379474238773395357793205161520837900)
      constant := (58198350454747408459645480813502185057717914655) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree118.table
  base := (61980490603385907078548639776322961300777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-99042639272700382924163875014696212708950)
      constant := (2983738349148048185888759745973399511128827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540830966898769105541/100000000000000000000)
  centralHi := (270415483449384552771/50000000000000000000)
  directionLo := (543137292785541189259/100000000000000000000)
  directionHi := (27156864639277059463/5000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree119.table
  base := (63534284106303165008051073458176765235357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-3905884971545041250189089757903760323041675800)
      constant := (118397441437408260128308725527171997459304575953) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree119.table
  base := (63534277483563374058167571695077673594319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-99881983673316487581939071084696212708950)
      constant := (3035023291764729870494904414417002329776844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (543137292785541189259/100000000000000000000)
  centralHi := (27156864639277059463/5000000000000000000)
  directionLo := (54543386663476984949/10000000000000000000)
  directionHi := (545433866634769849491/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree120.table
  base := (65104858743699990518757216851855692591511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10890000000000000000000000000000000000000000
      center := (124146)
      previous := (62073)
      next := (62073)
      square := (914046052270937972317188520230000000000000)
      linear := (-109408542620309278411983022228364175640046550)
      constant := (3344866943825084691172869678032746512537971729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree120.table
  base := (65104852732298347733909096152978927319913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-100721328073932592239714267154696212708950)
      constant := (3086744694950277114126059273434751689856913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54543386663476984949/10000000000000000000)
  centralHi := (545433866634769849491/100000000000000000000)
  directionLo := (136930202779076718501/25000000000000000000)
  directionHi := (109544162223261374801/20000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree121.table
  base := (16673055397378840590464617432548664784553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3240000000000000000000000000000000000000000
      center := (36936)
      previous := (18468)
      next := (18468)
      square := (271947585799617909119163526680000000000000)
      linear := (-32822562786092783433666841673871572917699800)
      constant := (1011983524972594580931461000283265143552525563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree121.table
  base := (66692216133398773319268121226190392458823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-101560672474548696897489463224696212708950)
      constant := (3138902558488497861995719231102811261350298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136930202779076718501/25000000000000000000)
  centralHi := (109544162223261374801/20000000000000000000)
  directionLo := (274999123174808650601/50000000000000000000)
  directionHi := (549998246349617301203/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree122.table
  base := (68296372444116473730002443771200288104163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196020000000000000000000000000000000000000000
      center := (2234628)
      previous := (1117314)
      next := (1117314)
      square := (16452828940876883501709393364140000000000000)
      linear := (-2002176329951659784057993442427905161520837900)
      constant := (62250915530762270900841850185342596435914240501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree122.table
  base := (68296367492330364448089514385994877726039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-102400016875164801555264659294696212708950)
      constant := (3191496882184857827737729154892463852971989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274999123174808650601/50000000000000000000)
  centralHi := (549998246349617301203/100000000000000000000)
  directionLo := (138066572494350422477/25000000000000000000)
  directionHi := (552266289977401689909/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree123.table
  base := (13983462225564150414270014379945446472109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-448575024743268037862031769685906702560186200)
      constant := (14063409287797840648314640848088356418716380645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree123.table
  base := (34958653317024883940942143488285634521397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-103239361275780906213039855364696212708950)
      constant := (3244527665864313658113600056147888350643219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138066572494350422477/25000000000000000000)
  centralHi := (552266289977401689909/100000000000000000000)
  directionLo := (554525057236508239933/100000000000000000000)
  directionHi := (277262528618254119967/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree124.table
  base := (8944379684863107118928678107365253019581/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-1017499446368876278350146242372627580760418950)
      constant := (32164141025327953638439486326504860927503398173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree124.table
  base := (71555033401054449159875687517467829517199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-104078705676397010870815051434696212708950)
      constant := (3297994909369362818662555183388633017472099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554525057236508239933/100000000000000000000)
  centralHi := (277262528618254119967/50000000000000000000)
  directionLo := (27838733051312785487/5000000000000000000)
  directionHi := (556774661026255709741/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree125.table
  base := (36604775675906155476148365272296017567429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-4102820348261597886042884011807860323041675800)
      constant := (130759472589211891817769165748785132894395082407) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree125.table
  base := (73209547651627625466278171310000737369843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-104918050077013115528590247504696212708950)
      constant := (3351898612558288526568808991916014031679218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27838733051312785487/5000000000000000000)
  centralHi := (556774661026255709741/100000000000000000000)
  directionLo := (139753802993570437499/25000000000000000000)
  directionHi := (559015211974281749997/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree126.table
  base := (37440426307769974463741678983258277456373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2420000000000000000000000000000000000000000
      center := (27588)
      previous := (13794)
      next := (13794)
      square := (203121344949097327181597448940000000000000)
      linear := (-25528659944738831226451747247686483475565900)
      constant := (820243265732993515681872054023158411060241657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree126.table
  base := (2340026539320585607703985128191867609201/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-105757394477629220186365443574696212708950)
      constant := (3406238775303580224477797267478001164158282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139753802993570437499/25000000000000000000)
  centralHi := (559015211974281749997/100000000000000000000)
  directionLo := (4384740769531447837/781250000000000000)
  directionHi := (561246818500025323137/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree127.table
  base := (76568941152185347474776538468520533050293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (4469256)
      previous := (2234628)
      next := (2234628)
      square := (32905657881753767003418786728280000000000000)
      linear := (-4168465473833783431327482096442560323041675800)
      constant := (135016373475288741114779916932522346124655285897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree127.table
  base := (38284469053110959205304997095054486763417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-106596738878245324844140639644696212708950)
      constant := (3461015397490512039699506258370818480545159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4384740769531447837/781250000000000000)
  centralHi := (561246818500025323137/100000000000000000000)
  directionLo := (563469586875946283821/100000000000000000000)
  directionHi := (281734793437973141911/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree128.table
  base := (78273816855639175872525344369652824174167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98010000000000000000000000000000000000000000
      center := (1117314)
      previous := (558657)
      next := (558657)
      square := (8226414470438441750854696682070000000000000)
      linear := (-1050322009154969050992445284689977580760418950)
      constant := (34292591466170839084776873830573293697466846767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree128.table
  base := (78273814092296618992707423248211620048821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-107436083278861429501915835714696212708950)
      constant := (3516228479015863428868117806268769233421621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell059.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563469586875946283821/100000000000000000000)
  centralHi := (281734793437973141911/50000000000000000000)
  directionLo := (565683621286579929769/100000000000000000000)
  directionHi := (56568362128657992977/10000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 395
  qDenominator := 792
  table := BinomialMassData.Q395_792.Degree129.table
  base := (79995479630408011615404441533634958688027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43560000000000000000000000000000000000000000
      center := (496584)
      previous := (248292)
      next := (248292)
      square := (3656184209083751889268754080920000000000000)
      linear := (-470456733267329886290231131230806702560186200)
      constant := (15482376245909452341949692613509498607260055487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q395_792.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 1
  qDenominator := 2
  table := BinomialMassData.Q1_2.Degree129.table
  base := (79995477123616237399937593525787324841037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (114)
      previous := (57)
      next := (57)
      square := (839344400616104657775196070000000000000)
      linear := (-108275427679477534159691031784696212708950)
      constant := (3571878019786767788190749693421193044568312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_2.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell059.Kernel129
