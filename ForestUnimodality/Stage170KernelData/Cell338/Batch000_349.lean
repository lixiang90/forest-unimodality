import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell338.Parameters
import ForestUnimodality.BinomialMassData.Q35_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q35_52.Batch050_099
import ForestUnimodality.BinomialMassData.Q35_52.Batch100_149
import ForestUnimodality.BinomialMassData.Q53_78.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_78.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_78.Batch100_149

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree000.table
  base := (2035479192613609792092965749/250000000000000000000000000)
  polynomial :=
    { denominator := 20800000000000000000000000000000000000000
      center := (35)
      previous := (0)
      next := (17)
      square := (226085818541627703304186528000000000000)
      linear := (-422253356005970897912860096000000000000)
      constant := (169351868825452334702134750316800000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree000.table
  base := (2035479192613609792092965749/250000000000000000000000000)
  polynomial :=
    { denominator := 31200000000000000000000000000000000000000
      center := (53)
      previous := (0)
      next := (25)
      square := (339128727812441554956279792000000000000)
      linear := (-633380034008956346869290144000000000000)
      constant := (254027803238178502053202125475200000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree001.table
  base := (1268987102211969721995492832895774556213/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270400000000000000000000000000000000000000
      center := (455)
      previous := (0)
      next := (221)
      square := (2939115641041160142954424864000000000000)
      linear := (-9445795452556106480690445488000000000000)
      constant := (1720696794092719414958815126765087199999976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree001.table
  base := (63279554140968104805998074587096420118343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-1066891097510217498514628614800000000000000)
      constant := (193068680244424041144498360104047309999999406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (29709371157209880491/100000000000000000000)
  directionHi := (7427342789302470123/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree002.table
  base := (4942496147502956050057857134901951512163/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-67011486385172956442568548640000000000000)
      constant := (6745832260816201142529023921787438444444376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree002.table
  base := (24580469132061789464903349087427656969099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-1516236661861702558831699339200000000000000)
      constant := (150997451844798325243479035247509864999998316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29709371157209880491/100000000000000000000)
  centralHi := (7427342789302470123/25000000000000000000)
  directionLo := (2625962226256391647/6250000000000000000)
  directionHi := (42015395620102266353/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree003.table
  base := (19227341849946074209152436157030468133629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-433969977537826902408424349200000000000000)
      constant := (26572060829349934461967948563555192916666408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree003.table
  base := (19073153061416459940076018510655745500493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-655194075404395873049590021200000000000000)
      constant := (39557955506287912572829007729109851874999804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2625962226256391647/6250000000000000000)
  centralHi := (42015395620102266353/100000000000000000000)
  directionLo := (51458140305208884029/100000000000000000000)
  directionHi := (5145814030520888403/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree004.table
  base := (14926236450760972112742918569124601039861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-532882523149789022604005955200000000000000)
      constant := (21082349382767701017770694829456460605892072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree004.table
  base := (29531830681529198822141816324892992517659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-2414927790564672679465840788000000000000000)
      constant := (93956882424425681053780023977124483238718678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51458140305208884029/100000000000000000000)
  centralHi := (5145814030520888403/10000000000000000000)
  directionLo := (29709371157209880491/50000000000000000000)
  directionHi := (59418742314419760983/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree005.table
  base := (11546438440365228302951861463499815661627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-631795068761751142799587561200000000000000)
      constant := (16904821277682885250290164209901750774519704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree005.table
  base := (22779871932333933196900789074360324992623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-2864273354916157739782911512400000000000000)
      constant := (75210998657517811305259536208704108627559166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29709371157209880491/50000000000000000000)
  centralHi := (59418742314419760983/100000000000000000000)
  directionLo := (2657286939051715361/4000000000000000000)
  directionHi := (33216086738146442013/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree006.table
  base := (8895340870457465280993126965023072912953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-730707614373713262995169167200000000000000)
      constant := (13779071919992024781167498297711194578312456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree006.table
  base := (2187119218238598088489809373801237337383/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-1104539639755880933366660745600000000000000)
      constant := (20413086944230967791646892957475637280850896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2657286939051715361/4000000000000000000)
  centralHi := (33216086738146442013/50000000000000000000)
  directionLo := (14554559982824800081/20000000000000000000)
  directionHi := (36386399957062000203/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree007.table
  base := (13606683534818068071091961144443536304511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-829620159985675383190750773200000000000000)
      constant := (11475799441349186147097064046893830541849436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree007.table
  base := (208411782594758884170257701588426315299/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-3762964483619127860417052961200000000000000)
      constant := (50993024515863457197659776444947542472931712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14554559982824800081/20000000000000000000)
  centralHi := (36386399957062000203/50000000000000000000)
  directionLo := (39301803845046287119/50000000000000000000)
  directionHi := (78603607690092574239/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree008.table
  base := (10296105818758026631364307797558773471451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-928532705597637503386332379200000000000000)
      constant := (9829534965825443816823842599149730866700876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree008.table
  base := (5027842862492062898100148402349406525743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-4212310047970612920734123685600000000000000)
      constant := (43716695760009674980932539983893789302620412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39301803845046287119/50000000000000000000)
  centralHi := (78603607690092574239/100000000000000000000)
  directionLo := (16806158248040906541/20000000000000000000)
  directionHi := (42015395620102266353/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree009.table
  base := (479294807646210159221778494223912475559/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-1027445251209599623581913985200000000000000)
      constant := (8711681884233477852355563478775837335646144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree009.table
  base := (932052772623788422283534401204151896523/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-1553885204107365993683731470000000000000000)
      constant := (12941536335956556531952182445668080184594576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16806158248040906541/20000000000000000000)
  centralHi := (42015395620102266353/50000000000000000000)
  directionLo := (89128113471629641473/100000000000000000000)
  directionHi := (44564056735814820737/50000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree010.table
  base := (5576488498951780871877723533378315686297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-1126357796821561743777495591200000000000000)
      constant := (8022173034264728869001949693563741403936772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree010.table
  base := (5391139688905362920461595652281027894787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-5111001176673583041368265134400000000000000)
      constant := (35862217165772724287184470148238886855942054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89128113471629641473/100000000000000000000)
  centralHi := (44564056735814820737/50000000000000000000)
  directionLo := (93949280708095597077/100000000000000000000)
  directionHi := (46974640354047798539/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree011.table
  base := (1952035046405681272463262416554575745663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-1225270342433523863973077197200000000000000)
      constant := (7683031507809267582591305214431786408136376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree011.table
  base := (1871849712689716185471939731312731944129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-5560346741025068101685335858800000000000000)
      constant := (34476225933088564777230044503406661148080836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93949280708095597077/100000000000000000000)
  centralHi := (46974640354047798539/50000000000000000000)
  directionLo := (6158427305366998931/6250000000000000000)
  directionHi := (98534836885871982897/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree012.table
  base := (2561446801350919371933108107174111407919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-1324182888045485984168658803200000000000000)
      constant := (7633407230731674773464685892449699311753244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree012.table
  base := (2423701018130055662385054129274032704689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-2003230768458851054000802194400000000000000)
      constant := (11463879125777982513725063274283869162554646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6158427305366998931/6250000000000000000)
  centralHi := (98534836885871982897/100000000000000000000)
  directionLo := (51458140305208884029/50000000000000000000)
  directionHi := (102916280610417768059/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree013.table
  base := (739138006662551022554742446867330886907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (875)
      previous := (0)
      next := (425)
      square := (5652145463540692582604663200000000000000)
      linear := (-109468879512111392643403108400000000000000)
      constant := (601980661371545716119800886724202412238328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree013.table
  base := (680338802318962027669059038204052344957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (3975)
      previous := (0)
      next := (1875)
      square := (25434654585933116621720984400000000000000)
      linear := (-496849066902156786332267485200000000000000)
      constant := (2722622407901933491817086716379496497439876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51458140305208884029/50000000000000000000)
  centralHi := (102916280610417768059/100000000000000000000)
  directionLo := (107118661069111140169/100000000000000000000)
  directionHi := (10711866106911114017/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree014.table
  base := (599513553388307704217166684149250478583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-1522007979269410224559822015200000000000000)
      constant := (8222845746570898657348263887484893323522108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree014.table
  base := (249812220562015591693129263506465734471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-6908383434079523282636548032000000000000000)
      constant := (37316263278686390967930912505973337528521564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107118661069111140169/100000000000000000000)
  centralHi := (10711866106911114017/10000000000000000000)
  directionLo := (11116228804678302837/10000000000000000000)
  directionHi := (111162288046783028371/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree015.table
  base := (-11796953818418720123473302387914446753/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-324184104976274468951080724240000000000000)
      constant := (1759108700036034939341080739421539667989944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree015.table
  base := (-202450763068783707570320986113461124967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-2452576332810336114317872918800000000000000)
      constant := (13342456919012877083376654849580950419283462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11116228804678302837/10000000000000000000)
  centralHi := (111162288046783028371/100000000000000000000)
  directionLo := (57531949859084420097/50000000000000000000)
  directionHi := (23012779943633768039/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree016.table
  base := (-354004098926856203789038802713417904109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-1719833070493334464950985227200000000000000)
      constant := (9520969441610063525868491314731458993644632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree016.table
  base := (-194798419318894445771494756214022858201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-7807074562782493403270689480800000000000000)
      constant := (43425063611664612342602924695987769861410232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57531949859084420097/50000000000000000000)
  centralHi := (23012779943633768039/20000000000000000000)
  directionLo := (29709371157209880491/25000000000000000000)
  directionHi := (23767496925767904393/20000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree017.table
  base := (-598588727027137813773336328214696989617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-1818745616105296585146566833200000000000000)
      constant := (10381158851639175931029474157503729670037816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree017.table
  base := (-314241722749050310908785618217884389173/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-8256420127133978463587760205200000000000000)
      constant := (47429146845305789935506586367624782752542936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29709371157209880491/25000000000000000000)
  centralHi := (23767496925767904393/20000000000000000000)
  directionLo := (61247437675927562041/50000000000000000000)
  directionHi := (122494875351855124083/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree018.table
  base := (-1606373497477872534369184583597115847831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-1917658161717258705342148439200000000000000)
      constant := (11361985905359722837085773734488349686866244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree018.table
  base := (-1656449868705790427652057030215375637549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-2901921897161821174634943643200000000000000)
      constant := (17325571175676266429107991381361609103525314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61247437675927562041/50000000000000000000)
  centralHi := (122494875351855124083/100000000000000000000)
  directionLo := (63023093430153399529/50000000000000000000)
  directionHi := (126046186860306799059/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree019.table
  base := (-1952044541848590535613597404813322428457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-2016570707329220825537730045200000000000000)
      constant := (12452331610294221156521432849596194038363068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree019.table
  base := (-1993881454516333984555618116751762435151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-9155111255836948584221901654000000000000000)
      constant := (57018365093044970926522808158141138672270658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63023093430153399529/50000000000000000000)
  centralHi := (126046186860306799059/100000000000000000000)
  directionLo := (6475007327520995307/5000000000000000000)
  directionHi := (129500146550419906141/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree020.table
  base := (-70223453316428155835646476941246239329/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-2115483252941182945733311651200000000000000)
      constant := (13643435061226203453044966830806961350835072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree020.table
  base := (-2282026282200772472872589168451539613911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-9604456820188433644538972378400000000000000)
      constant := (62515271527417019674064674037570416494482738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6475007327520995307/5000000000000000000)
  centralHi := (129500146550419906141/100000000000000000000)
  directionLo := (2657286939051715361/2000000000000000000)
  directionHi := (132864346952585768051/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree021.table
  base := (-1250956180359279250293253329111961218771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-2214395798553145065928893257200000000000000)
      constant := (14928386882158946008379204186290628432221608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree021.table
  base := (-2530927562783191607211694129781248874679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-3351267461513306234952014367600000000000000)
      constant := (22812293794069892262036611181101813641075494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2657286939051715361/2000000000000000000)
  centralHi := (132864346952585768051/100000000000000000000)
  directionLo := (136145442177452056717/100000000000000000000)
  directionHi := (68072721088726028359/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree022.table
  base := (-340549757601578656313685406280411000967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-2313308344165107186124474863200000000000000)
      constant := (16301733135387073689333847819835537306770464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree022.table
  base := (-343561788586875164746266000616837381923/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-10503147948891403765173113827200000000000000)
      constant := (74759135441606593254390019472588645473521872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136145442177452056717/100000000000000000000)
  centralHi := (68072721088726028359/50000000000000000000)
  directionLo := (17418662836277608023/12500000000000000000)
  directionHi := (27869860538044172837/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree023.table
  base := (-292098131892779904065564381716325600933/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-482444177955413861264011293840000000000000)
      constant := (3551833038249428738461236725769527787538584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree023.table
  base := (-1470480016273641518242728156971579081111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-10952493513242888825490184551600000000000000)
      constant := (81463071360244859364776357513484912870520676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17418662836277608023/12500000000000000000)
  centralHi := (27869860538044172837/20000000000000000000)
  directionLo := (28496227746708966903/20000000000000000000)
  directionHi := (35620284683386208629/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree024.table
  base := (-1548350636772147528652739953152633974119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-2511133435389031426515638075200000000000000)
      constant := (19297276592126522439370599327337638866991112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree024.table
  base := (-622648303185437743683560485941210110771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2028000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (22043367307808701072158186480000000000000)
      linear := (-760122605172958259053817018400000000000000)
      constant := (5902248819235757257876716824375612947678206) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28496227746708966903/20000000000000000000)
  centralHi := (35620284683386208629/25000000000000000000)
  directionLo := (145545599828248000811/100000000000000000000)
  directionHi := (36386399957062000203/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree025.table
  base := (-130221792208901301803276367137333132361/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270400000000000000000000000000000000000000
      center := (455)
      previous := (0)
      next := (221)
      square := (2939115641041160142954424864000000000000)
      linear := (-104401839240039741868448787248000000000000)
      constant := (836534888270654769006480103065162802523964) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree025.table
  base := (-1634609882020152811814464775466279923643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-11851184641945858946124326000400000000000000)
      constant := (95959312208645695320013720378563152944555988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145545599828248000811/100000000000000000000)
  centralHi := (36386399957062000203/25000000000000000000)
  directionLo := (29709371157209880491/20000000000000000000)
  directionHi := (18568356973256175307/12500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree026.table
  base := (-425083548933850265228165905714961813369/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (875)
      previous := (0)
      next := (425)
      square := (5652145463540692582604663200000000000000)
      linear := (-208381425124073512838984714400000000000000)
      constant := (1738870635105467660924637380222575885638496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree026.table
  base := (-136478411191553275147316386458873625631/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 93600000000000000000000000000000000000000
      center := (159)
      previous := (0)
      next := (75)
      square := (1017386183437324664868839376000000000000)
      linear := (-37847785250145673865973528384000000000000)
      constant := (319170725725367329290330321776623571602346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29709371157209880491/20000000000000000000)
  centralHi := (18568356973256175307/12500000000000000000)
  directionLo := (9468041454198989737/6250000000000000000)
  directionHi := (151488663267183835793/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree027.table
  base := (-706914527734090778897837058492116444109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-561574214444983557420476578640000000000000)
      constant := (4874284866205372173528983285109329283782316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree027.table
  base := (-3543885952921638570597817637740586147037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-4249958590216276355586155816400000000000000)
      constant := (37279960938072117706490890396031045646904482) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9468041454198989737/6250000000000000000)
  centralHi := (151488663267183835793/100000000000000000000)
  directionLo := (19296802614453331511/12500000000000000000)
  directionHi := (154374420915626652089/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree028.table
  base := (-1829619863133634718016253086318032618863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-2906783617836879907297964499200000000000000)
      constant := (26210350477428364708715594575298019899297224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree028.table
  base := (-183345644902918728128297187598335178203/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (10335)
      previous := (0)
      next := (4875)
      square := (66130101923426103216474559440000000000000)
      linear := (-2639844267000062825415107634720000000000000)
      constant := (24056334849677727355705744640503457551625896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19296802614453331511/12500000000000000000)
  centralHi := (154374420915626652089/100000000000000000000)
  directionLo := (39301803845046287119/25000000000000000000)
  directionHi := (157207215380185148477/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree029.table
  base := (-1888120874418787573837013186241872965951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-3005696163448842027493546105200000000000000)
      constant := (28121033959641994468008454527450987750034248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree029.table
  base := (-3782557285635011931443174519891614228141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-13648566899351799187392608898000000000000000)
      constant := (129051247972795005938729903839789709517995078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39301803845046287119/25000000000000000000)
  centralHi := (157207215380185148477/100000000000000000000)
  directionLo := (3999746499947588573/2500000000000000000)
  directionHi := (159989859997903542921/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree030.table
  base := (-777365239097059045568019551502631807493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-620921741812160829537825542240000000000000)
      constant := (6020526295006699477477456484184220898134732) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree030.table
  base := (-1946009718297207006832773253509217504307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-4699304154567761415903226540800000000000000)
      constant := (46048317537042423443545929955883306901265404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3999746499947588573/2500000000000000000)
  centralHi := (159989859997903542921/100000000000000000000)
  directionLo := (16272492752097212289/10000000000000000000)
  directionHi := (162724927520972122891/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree031.table
  base := (-3991983448430252206544952753552168223881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-3203521254672766267884709317200000000000000)
      constant := (32154473525222273436562457135848734280656444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree031.table
  base := (-1998125038072112148060535152363767634561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-14547258028054769308026750346800000000000000)
      constant := (147559896057303778467139053067118837711330876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16272492752097212289/10000000000000000000)
  centralHi := (162724927520972122891/100000000000000000000)
  directionLo := (33082955594240660261/20000000000000000000)
  directionHi := (82707388985601650653/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree032.table
  base := (-1023125031368515982336759912389473219109/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-3302433800284728388080290923200000000000000)
      constant := (34276028356574428951936467628898864415529264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree032.table
  base := (-4096002573204164565030148674732243733763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-14996603592406254368343821071200000000000000)
      constant := (157293786563070736674551228237064514561892954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33082955594240660261/20000000000000000000)
  centralHi := (82707388985601650653/50000000000000000000)
  directionLo := (16806158248040906541/10000000000000000000)
  directionHi := (168061582480409065411/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree033.table
  base := (-4189001266541863197522737790252177423479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-3401346345896690508275872529200000000000000)
      constant := (36466873442100574159846481463039528061728196) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree033.table
  base := (-4191874160551722480484567574930650808339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-5148649718919246476220297265200000000000000)
      constant := (55781602448773009163625034164520320080344254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16806158248040906541/10000000000000000000)
  centralHi := (168061582480409065411/100000000000000000000)
  directionLo := (853336719009210831/500000000000000000)
  directionHi := (170667343801842166201/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree034.table
  base := (-535247965067490826355897179638698170911/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-3500258891508652628471454135200000000000000)
      constant := (38726672911940066078844510581513920291713312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree034.table
  base := (-53554231032427967224706661889286716067/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (10335)
      previous := (0)
      next := (4875)
      square := (66130101923426103216474559440000000000000)
      linear := (-3179058944221844897795592504000000000000000)
      constant := (35542303516152304931508677069884636955586976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (853336719009210831/500000000000000000)
  centralHi := (170667343801842166201/100000000000000000000)
  directionLo := (173233914043795269833/100000000000000000000)
  directionHi := (86616957021897634917/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree035.table
  base := (-4371842585107957847975706142104857815753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-3599171437120614748667035741200000000000000)
      constant := (41055159680088465022159540039187116116550972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree035.table
  base := (-1093442827981966679771378555647784187761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-16344640285460709549295033244400000000000000)
      constant := (188392774166160717176431330831377762003324152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173233914043795269833/100000000000000000000)
  centralHi := (86616957021897634917/50000000000000000000)
  directionLo := (175763010071772218643/100000000000000000000)
  directionHi := (43940752517943054661/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree036.table
  base := (-1114723039347027885343199527344743207139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-3698083982732576868862617347200000000000000)
      constant := (43452121281677674458245585274059814367896144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree036.table
  base := (-4460470880607355649238252474226176802443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-5597995283270731536537367989600000000000000)
      constant := (66462556626868690105050264186334656722322798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (175763010071772218643/100000000000000000000)
  centralHi := (43940752517943054661/25000000000000000000)
  directionLo := (89128113471629641473/50000000000000000000)
  directionHi := (178256226943259282947/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree037.table
  base := (-4543382544610446538171783217610636132889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-3796996528344538989058198953200000000000000)
      constant := (45917388644220174606440515288145209974167036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree037.table
  base := (-908934792558870394103960882550216462469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (10335)
      previous := (0)
      next := (4875)
      square := (66130101923426103216474559440000000000000)
      linear := (-3448666282832735933985834938640000000000000)
      constant := (42139096891419570291951805606102241521169302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89128113471629641473/50000000000000000000)
  centralHi := (178256226943259282947/100000000000000000000)
  directionLo := (11294690604612432489/6250000000000000000)
  directionHi := (7228601986951956793/4000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree038.table
  base := (-289094552527485747677104054881037238351/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-3895909073956501109253780559200000000000000)
      constant := (48450827180398554498608691775406701229995584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree038.table
  base := (-144580268849336125581809147682965930143/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-17692676978515164730246245417600000000000000)
      constant := (222315645863689383789093984829949364496159808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11294690604612432489/6250000000000000000)
  centralHi := (7228601986951956793/4000000000000000000)
  directionLo := (36628172716181442311/20000000000000000000)
  directionHi := (45785215895226802889/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree039.table
  base := (-941088316428330312703841317358078628029/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104000000000000000000000000000000000000000
      center := (175)
      previous := (0)
      next := (85)
      square := (1130429092708138516520932640000000000000)
      linear := (-61458794147207126606913264080000000000000)
      constant := (785420457215712200630668286347379911342492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree039.table
  base := (-2353152097775972985237111964471377459887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (1325)
      previous := (0)
      next := (625)
      square := (8478218195311038873906994800000000000000)
      linear := (-465180065201708968988802978000000000000000)
      constant := (6006351272935058843305102352242465116257628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36628172716181442311/20000000000000000000)
  centralHi := (45785215895226802889/25000000000000000000)
  directionLo := (92767481705225403549/50000000000000000000)
  directionHi := (185534963410450807099/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree040.table
  base := (-4783295053423768182372698444944765270739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-4093734165180425349644943771200000000000000)
      constant := (53721810892301996632305215691217338676980436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree040.table
  base := (-4783999466720072799291573431904976471353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-18591368107218134850880386866400000000000000)
      constant := (246491284632487273498691205956145061574144174) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92767481705225403549/50000000000000000000)
  centralHi := (185534963410450807099/100000000000000000000)
  directionLo := (37579712283238238831/20000000000000000000)
  directionHi := (46974640354047798539/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree041.table
  base := (-4859173879501306003335278903278351268953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-4192646710792387469840525377200000000000000)
      constant := (56459202677595200764199813418633834542187772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree041.table
  base := (-97194976073796438345416558956189433007/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1216800000000000000000000000000000000000000
      center := (2067)
      previous := (0)
      next := (975)
      square := (13226020384685220643294911888000000000000)
      linear := (-761628546862784796447898303632000000000000)
      constant := (10361844548098999303782221204194543489585412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37579712283238238831/20000000000000000000)
  centralHi := (46974640354047798539/25000000000000000000)
  directionLo := (3804655890712379707/2000000000000000000)
  directionHi := (190232794535618985351/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree042.table
  base := (-4933158267660192225237053975587256829103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-4291559256404349590036106983200000000000000)
      constant := (59264450854775618650268080129503014383526372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree042.table
  base := (-986725453962905725146481242474486457599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2028000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (22043367307808701072158186480000000000000)
      linear := (-1299337282394740331434301887680000000000000)
      constant := (18127463900780638412658350025970870731994614) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3804655890712379707/2000000000000000000)
  centralHi := (190232794535618985351/100000000000000000000)
  directionLo := (24067341347829337451/12500000000000000000)
  directionHi := (192538730782634699609/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree043.table
  base := (-1001062434597493112101192945254189202747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-878094360403262342046337717840000000000000)
      constant := (12427502438040882424181745532858168098943028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree043.table
  base := (-1251423645738879120055270179214816068339/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-19939404800272590031831599039600000000000000)
      constant := (285088637398456908028683168891814118080451048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24067341347829337451/12500000000000000000)
  centralHi := (192538730782634699609/100000000000000000000)
  directionLo := (48704343739768695039/25000000000000000000)
  directionHi := (194817374959074780157/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree044.table
  base := (-253784330540343662938392518009884820477/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-897876869525654766085454039040000000000000)
      constant := (13015670439504545607074937744101271445430192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree044.table
  base := (-5075998271474811253120802006463945930129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-20388750364624075092148669764000000000000000)
      constant := (298576005781439695711387308053136676480547582) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48704343739768695039/25000000000000000000)
  centralHi := (194817374959074780157/100000000000000000000)
  directionLo := (6158427305366998931/3125000000000000000)
  directionHi := (197069673771743965793/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree045.table
  base := (-5144322291411191369286298678748118113031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-4588296893240235950622851801200000000000000)
      constant := (68086943356572649784363777944416272155591044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree045.table
  base := (-5144576178733065838631901247002221573917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-6946031976325186717488580162800000000000000)
      constant := (104124649513718277711276753489039747324048162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6158427305366998931/3125000000000000000)
  centralHi := (197069673771743965793/100000000000000000000)
  directionLo := (49824130107219663019/25000000000000000000)
  directionHi := (199296520428878652077/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree046.table
  base := (-2605625858170104578954389634064209938679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-4687209438852198070818433407200000000000000)
      constant := (71163263696313279824163105895745188162905992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree046.table
  base := (-2605729225569201253992623478285782981741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-21287441493327045212782811212800000000000000)
      constant := (326482373972228812346927724101709296339087756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49824130107219663019/25000000000000000000)
  centralHi := (199296520428878652077/100000000000000000000)
  directionLo := (50374689694835404179/25000000000000000000)
  directionHi := (201498758779341616717/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree047.table
  base := (-527650084668771561181768085548158299053/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-957224396892832038202803002640000000000000)
      constant := (14861459133409043359887475558988889979680344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree047.table
  base := (-5276669116653728388276685391311305074989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-21736787057678530273099881937200000000000000)
      constant := (340901208981598469870054134645731009961883462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50374689694835404179/25000000000000000000)
  centralHi := (201498758779341616717/100000000000000000000)
  directionLo := (25459648381118501139/12500000000000000000)
  directionHi := (203677187048948009113/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree048.table
  base := (-5340090431138025345238323972658767204791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-4885034530076122311209596619200000000000000)
      constant := (77519025242657864030970276962482673369561284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree048.table
  base := (-5340227338433358603775232932737011790641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-7395377540676671777805650887200000000000000)
      constant := (118543465091649459698394381422204670044290026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25459648381118501139/12500000000000000000)
  centralHi := (203677187048948009113/100000000000000000000)
  directionLo := (205832561220835536117/100000000000000000000)
  directionHi := (102916280610417768059/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree049.table
  base := (-1080407412675520713369586431203689991679/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-996789415137616886281035645040000000000000)
      constant := (16159688241163834207539200057556305565624996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree049.table
  base := (-270107420533826714524036289276416430263/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (10335)
      previous := (0)
      next := (4875)
      square := (66130101923426103216474559440000000000000)
      linear := (-4527095637276300078746804677200000000000000)
      constant := (74133977265464889697320650245944564876559816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205832561220835536117/100000000000000000000)
  centralHi := (102916280610417768059/50000000000000000000)
  directionLo := (207965598100469163437/100000000000000000000)
  directionHi := (103982799050234581719/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree050.table
  base := (-2731177012105624753941440534340925141207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-5082859621300046551600759831200000000000000)
      constant := (84145534578705093539298757822571069209088136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree050.table
  base := (-1365611137468575610129708154745012710947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-23084823750732985454051094110400000000000000)
      constant := (386019644976160913094268171443062685333196904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207965598100469163437/100000000000000000000)
  centralHi := (103982799050234581719/50000000000000000000)
  directionLo := (210076978100511331763/100000000000000000000)
  directionHi := (52519244525127832941/25000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree051.table
  base := (-2760525976177523466813052741227814728383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-5181772166912008671796341437200000000000000)
      constant := (87560298169543558910447285661109994487226184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree051.table
  base := (-5521125523614825371142745480992919600017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-7844723105028156838122721611600000000000000)
      constant := (133893213836151527716364564898973179525582762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210076978100511331763/100000000000000000000)
  centralHi := (52519244525127832941/25000000000000000000)
  directionLo := (8486693911049185191/4000000000000000000)
  directionHi := (13260459236014351861/6250000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree052.table
  base := (-2789069689432055160240146709467640523957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (875)
      previous := (0)
      next := (425)
      square := (5652145463540692582604663200000000000000)
      linear := (-406206516347997753230147926400000000000000)
      constant := (7003286631641639212699489746215365385508472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree052.table
  base := (-5578199150392035728367445015955162351857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (3975)
      previous := (0)
      next := (1875)
      square := (25434654585933116621720984400000000000000)
      linear := (-1844885759956611967283479658400000000000000)
      constant := (32126911703103608887838634605466492009665462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8486693911049185191/4000000000000000000)
  centralHi := (13260459236014351861/6250000000000000000)
  directionLo := (214237322138222280339/100000000000000000000)
  directionHi := (10711866106911114017/5000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree053.table
  base := (-5633623152995535857607034307060637070843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-5379597258135932912187504649200000000000000)
      constant := (94592814074000549079363766487677009340110132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree053.table
  base := (-1126734339390785826606497124183494085347/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (10335)
      previous := (0)
      next := (4875)
      square := (66130101923426103216474559440000000000000)
      linear := (-4886572088757488127000461256720000000000000)
      constant := (86786051561678101518819982497933810992374426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214237322138222280339/100000000000000000000)
  centralHi := (10711866106911114017/5000000000000000000)
  directionLo := (54071871691477261511/25000000000000000000)
  directionHi := (43257497353181809209/20000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree054.table
  base := (-177734649425663670716259659632355217397/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-5478509803747895032383086255200000000000000)
      constant := (98210558034875863044748633891832891937268096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree054.table
  base := (-2843774097125598997871572911527288804507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-8294068669379641898439792336000000000000000)
      constant := (150173614402811117664208475091022658304459804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54071871691477261511/25000000000000000000)
  centralHi := (43257497353181809209/20000000000000000000)
  directionLo := (3411224995974562519/1562500000000000000)
  directionHi := (218318399742372001217/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree055.table
  base := (-5739800699787146075967188747941695461461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-5577422349359857152578667861200000000000000)
      constant := (101895955095876202346114148967641413868052364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree055.table
  base := (-5739832688705521763512006990233483560137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-25331551572490410755636447732400000000000000)
      constant := (467421596031260702859666515700209743010063246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3411224995974562519/1562500000000000000)
  centralHi := (218318399742372001217/100000000000000000000)
  directionLo := (220330593428663440889/100000000000000000000)
  directionHi := (22033059342866344089/10000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree056.table
  base := (-289525124321179734397572103500557572979/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-1135266978994363854554849893440000000000000)
      constant := (21129800567528932376281312795334492322664784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree056.table
  base := (-5790528442073545936505321143948075671183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-25780897136841895815953518456800000000000000)
      constant := (484632506354608841583717445121709953808261314) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220330593428663440889/100000000000000000000)
  centralHi := (22033059342866344089/10000000000000000000)
  directionLo := (11116228804678302837/5000000000000000000)
  directionHi := (222324576093566056741/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree057.table
  base := (-729952129544460910387157024028426743071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-5775247440583781392969831073200000000000000)
      constant := (109469699303279471357290328427304268173472032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree057.table
  base := (-1459909522612691241147748205042023699721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-8743414233731126958756863060400000000000000)
      constant := (167384522053158425016093349313049551873931624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11116228804678302837/5000000000000000000)
  centralHi := (222324576093566056741/100000000000000000000)
  directionLo := (89720333365177103/40000000000000000)
  directionHi := (224300833412942757501/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree058.table
  base := (-588714669749072080268031015439995569121/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-1174831997239148702633082535840000000000000)
      constant := (22671608581119059608292616657725125990548408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree058.table
  base := (-5887163770791546275760904304909331309841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-26679588265544865936587659905600000000000000)
      constant := (519984768945244817537403018238465814155463678) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89720333365177103/40000000000000000)
  centralHi := (224300833412942757501/100000000000000000000)
  directionLo := (226259829851207906589/100000000000000000000)
  directionHi := (22625982985120790659/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree059.table
  base := (-1483273345063067260940061936519328420617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-5973072531807705633360994285200000000000000)
      constant := (117314032353145806047112509358901735950651632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree059.table
  base := (-2966553610800282871559729779281497188263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-27128933829896350996904730630000000000000000)
      constant := (538126109423386245045102759172151371106607908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226259829851207906589/100000000000000000000)
  centralHi := (22625982985120790659/10000000000000000000)
  directionLo := (57050502484013236151/25000000000000000000)
  directionHi := (45640401987210588921/20000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree060.table
  base := (-1195491728978421053631358955594228783201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-1214397015483933550711315178240000000000000)
      constant := (24267533318240159329849694398018301342556124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree060.table
  base := (-747183732885558609528548202916574259679/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-9192759798082612019073933784800000000000000)
      constant := (185525861091210313977097499025940749605483952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57050502484013236151/25000000000000000000)
  centralHi := (45640401987210588921/20000000000000000000)
  directionLo := (230127799436337680389/100000000000000000000)
  directionHi := (23012779943633768039/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree061.table
  base := (-3010121885583064214096829314803515898741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-6170897623031629873752157497200000000000000)
      constant := (125428944754645282156100144993635646504902168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree061.table
  base := (-1505063215241839188920854261870221803103/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-28027624958599321117538872078800000000000000)
      constant := (575339186949846192708800007459663141099842696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230127799436337680389/100000000000000000000)
  centralHi := (23012779943633768039/10000000000000000000)
  directionLo := (232037606451988974919/100000000000000000000)
  directionHi := (5800940161299724373/2500000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree062.table
  base := (-6061449813948819148087628582126033684713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-6269810168643591993947739103200000000000000)
      constant := (129587866130384113665696978815482801229134012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree062.table
  base := (-3030728588655829703489650407955006312843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-28476970522950806177855942803200000000000000)
      constant := (594410917525438085240070269989601741592663188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232037606451988974919/100000000000000000000)
  centralHi := (5800940161299724373/2500000000000000000)
  directionLo := (9357272896952399553/4000000000000000000)
  directionHi := (116965911211904994413/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree063.table
  base := (-6101077647634778386537037934625378010131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-6368722714255554114143320709200000000000000)
      constant := (133814430127326540929958900145443244465151444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree063.table
  base := (-381317725687567147258819685365475818183/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-9642105362434097079391004509200000000000000)
      constant := (204597590856734137216978332426130520325799008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9357272896952399553/4000000000000000000)
  centralHi := (116965911211904994413/50000000000000000000)
  directionLo := (117905411535138861357/50000000000000000000)
  directionHi := (47162164614055544543/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree064.table
  base := (-1227825600319535348861329912730912091223/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-1293527051973503246867780463040000000000000)
      constant := (27621727250483192524553785855793903426333252) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree064.table
  base := (-6139132829998014175198920231251625831989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-29375661651653776298490084252000000000000000)
      constant := (633484750052197512897278744573332554219089462) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117905411535138861357/50000000000000000000)
  centralHi := (47162164614055544543/20000000000000000000)
  directionLo := (237674969257679043929/100000000000000000000)
  directionHi := (23767496925767904393/10000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree065.table
  base := (-6175601488516319538764360890501776983961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (875)
      previous := (0)
      next := (425)
      square := (5652145463540692582604663200000000000000)
      linear := (-505119061959959873425729532400000000000000)
      constant := (10959268007037038949968182119943907596834028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree065.table
  base := (-1235121079411093889238151168661876009441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 468000000000000000000000000000000000000000
      center := (795)
      previous := (0)
      next := (375)
      square := (5086930917186623324344196880000000000000)
      linear := (-458846264861619405520110076560000000000000)
      constant := (10053643819377366025054489177433121013790806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237674969257679043929/100000000000000000000)
  centralHi := (23767496925767904393/10000000000000000000)
  directionLo := (119762303904646403741/50000000000000000000)
  directionHi := (239524607809292807483/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree066.table
  base := (-3105249313505268528402843671666807409743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-6665460351091440474730065527200000000000000)
      constant := (146899973293936166836469846556906476382027464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree066.table
  base := (-621050179021937737381601240950851573137/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2028000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (22043367307808701072158186480000000000000)
      linear := (-2018290185357116427941615046720000000000000)
      constant := (44919937715865367124535240461991673009678164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119762303904646403741/50000000000000000000)
  centralHi := (239524607809292807483/100000000000000000000)
  directionLo := (60340018064689243247/25000000000000000000)
  directionHi := (241360072258756972989/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree067.table
  base := (-780477482467146040230441275312786015507/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-6764372896703402594925647133200000000000000)
      constant := (151397103560543920903592245006358453228138144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree067.table
  base := (-390238901199015957818420501658739856153/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-30723698344708231479441296425200000000000000)
      constant := (694421401241261936785264219873365813721321184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60340018064689243247/25000000000000000000)
  centralHi := (241360072258756972989/100000000000000000000)
  directionLo := (6079542088806382797/2500000000000000000)
  directionHi := (243181683552255311881/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree068.table
  base := (-3137782783931671923588429278272812166439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-6863285442315364715121228739200000000000000)
      constant := (155961874633635788323963459803775157950974472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree068.table
  base := (-6275567638347535076951218445956300995721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-31173043909059716539758367149600000000000000)
      constant := (715353853691296093914844866847400932371016718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6079542088806382797/2500000000000000000)
  centralHi := (243181683552255311881/100000000000000000000)
  directionLo := (61247437675927562041/25000000000000000000)
  directionHi := (48997950140742049633/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree069.table
  base := (-3152868041324254541372012024651012032029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-6962197987927326835316810345200000000000000)
      constant := (160594286289280383973425165237921831732696792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree069.table
  base := (-788217219654402589087939059316487522639/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-10540796491137067200025145958000000000000000)
      constant := (245532140715501624611772368073924653216352432) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61247437675927562041/25000000000000000000)
  centralHi := (48997950140742049633/20000000000000000000)
  directionLo := (9871382856270782927/4000000000000000000)
  directionHi := (30848071425846196647/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree070.table
  base := (-6334331694718549552353867352725382728809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-7061110533539288955512391951200000000000000)
      constant := (165294338331014609237882585014557641275325116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree070.table
  base := (-3167166524417029698812936289813130518207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-32071735037762686660392508598400000000000000)
      constant := (758149105776462591669916625570776913927228612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9871382856270782927/4000000000000000000)
  centralHi := (30848071425846196647/12500000000000000000)
  directionLo := (1242832163035095869/500000000000000000)
  directionHi := (248566432607019173801/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree071.table
  base := (-1590338165374331063126920786794213570283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-7160023079151251075707973557200000000000000)
      constant := (170062030584819935435700843929758446505954768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree071.table
  base := (-1272270751251221078893140577644238704761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (10335)
      previous := (0)
      next := (4875)
      square := (66130101923426103216474559440000000000000)
      linear := (-6504216120422834344141915864560000000000000)
      constant := (156002380768324475670273165508026225860117038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1242832163035095869/500000000000000000)
  centralHi := (248566432607019173801/100000000000000000000)
  directionLo := (250335611037536285827/100000000000000000000)
  directionHi := (62583902759384071457/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree072.table
  base := (-1277359842633357580539123575695859311523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-1451787124952642639180711032640000000000000)
      constant := (34979472579018672235300920597229599105410452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree072.table
  base := (-1277360019614921930685063133381014960491/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2028000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (22043367307808701072158186480000000000000)
      linear := (-2198028411097710452068443336480000000000000)
      constant := (53478987711805626965943285080991650830062126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250335611037536285827/100000000000000000000)
  centralHi := (62583902759384071457/25000000000000000000)
  directionLo := (63023093430153399529/25000000000000000000)
  directionHi := (252092373720613598117/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree073.table
  base := (-6410671557451827958883291222384596551691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-7357848170375175316099136769200000000000000)
      constant := (179800335121412862540061103282918012731056884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree073.table
  base := (-801334034075124938183275281045899898003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-33419771730817141841343720771600000000000000)
      constant := (824667840679585308142482114960966980082198992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63023093430153399529/25000000000000000000)
  centralHi := (252092373720613598117/100000000000000000000)
  directionLo := (253836978438229853987/100000000000000000000)
  directionHi := (63459244609557463497/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree074.table
  base := (-3216484941733044716434831116792448546107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-7456760715987137436294718375200000000000000)
      constant := (184770947135937615498394248499096609565663336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree074.table
  base := (-6432970461317684653252492530945210848907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-33869117295168626901660791496000000000000000)
      constant := (847460978297055598995860060627664668597624906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (253836978438229853987/100000000000000000000)
  centralHi := (63459244609557463497/25000000000000000000)
  directionLo := (255569674173613998753/100000000000000000000)
  directionHi := (127784837086806999377/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree075.table
  base := (-6453694364807326378781246993846436565629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-7555673261599099556490299981200000000000000)
      constant := (189809198821315538310914513763409808881634796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree075.table
  base := (-1613423707909410666017046686837404222957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-11439487619840037320659287406800000000000000)
      constant := (290188076006741666429868394835687488471686408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255569674173613998753/100000000000000000000)
  centralHi := (127784837086806999377/50000000000000000000)
  directionLo := (128645350763022210073/50000000000000000000)
  directionHi := (257290701526044420147/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree076.table
  base := (-6472845162052746527039901458634471395121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-7654585807211061676685881587200000000000000)
      constant := (194915090068996438551856724449963097336898204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree076.table
  base := (-6472845539126898612915086071676393296259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-34767808423871597022294932944800000000000000)
      constant := (893977589375861660745562007427560411592780122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128645350763022210073/50000000000000000000)
  centralHi := (257290701526044420147/100000000000000000000)
  directionLo := (6475007327520995307/2500000000000000000)
  directionHi := (259000293100839812281/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree077.table
  base := (-6490422424774446872837618610231881683491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-7753498352823023796881463193200000000000000)
      constant := (200088620777869578652471093302733247981960084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree077.table
  base := (-3245211364649144949359374368480510128533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-35217153988223082082612003669200000000000000)
      constant := (917701061921315531996198981244264576378005228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6475007327520995307/2500000000000000000)
  centralHi := (259000293100839812281/100000000000000000000)
  directionLo := (10427946955053255177/4000000000000000000)
  directionHi := (130349336938165689713/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree078.table
  base := (-1626606573292703080121896801904858177579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (875)
      previous := (0)
      next := (425)
      square := (5652145463540692582604663200000000000000)
      linear := (-604031607571921993621311138400000000000000)
      constant := (15794599296396988493649377286203789499063568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree078.table
  base := (-6506426539062843728199344527727520429053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (1325)
      previous := (0)
      next := (625)
      square := (8478218195311038873906994800000000000000)
      linear := (-914525629553194029305873702400000000000000)
      constant := (24147042185643673545607008960837253406533866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10427946955053255177/4000000000000000000)
  centralHi := (130349336938165689713/50000000000000000000)
  directionLo := (262386061549455480161/100000000000000000000)
  directionHi := (131193030774727740081/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree079.table
  base := (-1630214224847605648787318583404971833591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-7951323444046948037272626405200000000000000)
      constant := (210638600205537813952561358955722956161969936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree079.table
  base := (-6520857097907534320319347138000805615101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-36115845116926052203246145118000000000000000)
      constant := (966078338938325494018901267135501549318862758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262386061549455480161/100000000000000000000)
  centralHi := (131193030774727740081/50000000000000000000)
  directionLo := (132031333430734817679/50000000000000000000)
  directionHi := (264062666861469635359/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree080.table
  base := (-6533714368609592681852958584118984034609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-8050235989658910157468208011200000000000000)
      constant := (216015048750381280327948987677135566792604316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree080.table
  base := (-6533714528854209289989950161165825555121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-36565190681277537263563215842400000000000000)
      constant := (990732142641749748772322883321733558661321918) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132031333430734817679/50000000000000000000)
  centralHi := (264062666861469635359/100000000000000000000)
  directionLo := (265728693905171536101/100000000000000000000)
  directionHi := (132864346952585768051/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree081.table
  base := (-261799952796494728447683961846156432013/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270400000000000000000000000000000000000000
      center := (455)
      previous := (0)
      next := (221)
      square := (2939115641041160142954424864000000000000)
      linear := (-325965941410834891106551584688000000000000)
      constant := (8858365456287617387892944501681998251959212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree081.table
  base := (-163624973731083698474750114790825177137/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2028000000000000000000000000000000000000000
      center := (3445)
      previous := (0)
      next := (1625)
      square := (22043367307808701072158186480000000000000)
      linear := (-2467635749708601488258685771120000000000000)
      constant := (67713070399561752966861795553756826163064656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265728693905171536101/100000000000000000000)
  centralHi := (132864346952585768051/50000000000000000000)
  directionLo := (13369217020744446221/5000000000000000000)
  directionHi := (267384340414888924421/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree082.table
  base := (-1310942073402395780081096154751447949077/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-1649612216176566879571874244640000000000000)
      constant := (45394172619819026754366362970788021186423948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree082.table
  base := (-6554710471377456028894117207690945565389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-37463881809980507384197357291200000000000000)
      constant := (1040970078651730908684003463269804143590086662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13369217020744446221/5000000000000000000)
  centralHi := (267384340414888924421/100000000000000000000)
  directionLo := (67257449510101693727/25000000000000000000)
  directionHi := (269029798040406774909/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree083.table
  base := (-1640712279711229383236694529878230156857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-8346973626494796518054952829200000000000000)
      constant := (232550228752454308429858910750459265655858672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree083.table
  base := (-820356150381481099764638408116353221927/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-37913227374331992444514428015600000000000000)
      constant := (1066554210288750242360294593036580427991184528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67257449510101693727/25000000000000000000)
  centralHi := (269029798040406774909/100000000000000000000)
  directionLo := (135332626302953006109/50000000000000000000)
  directionHi := (270665252605906012219/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree084.table
  base := (-6569415180062558006770291623954402490441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-8445886172106758638250534435200000000000000)
      constant := (238197233296523629916387793066206823916461884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree084.table
  base := (-3284707623997478980182370174658003268431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-12787524312894492501610499580000000000000000)
      constant := (364149483529647468752902461231393569371621932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135332626302953006109/50000000000000000000)
  centralHi := (270665252605906012219/100000000000000000000)
  directionLo := (54458176870980822687/20000000000000000000)
  directionHi := (68072721088726028359/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree085.table
  base := (-6574408651440233877388833147760136332737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-8544798717718720758446116041200000000000000)
      constant := (243911876663178972747891800983364147839069788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree085.table
  base := (-6574408706235825944101200537517779552397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-38811918503034962565148569464400000000000000)
      constant := (1118652799248019053311853787281370914601608326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54458176870980822687/20000000000000000000)
  centralHi := (68072721088726028359/25000000000000000000)
  directionLo := (273906868182111527067/100000000000000000000)
  directionHi := (68476717045527881767/25000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree086.table
  base := (-1315565926043942695511498005042648007261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-1728742252666136575728339529440000000000000)
      constant := (49938831757336980306285699092791169947091564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree086.table
  base := (-657782967441288836992180269758093468741/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6084000000000000000000000000000000000000000
      center := (10335)
      previous := (0)
      next := (4875)
      square := (66130101923426103216474559440000000000000)
      linear := (-7852252813477289525093128037760000000000000)
      constant := (229033451194401212472376571193911759336179756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273906868182111527067/100000000000000000000)
  centralHi := (68476717045527881767/25000000000000000000)
  directionLo := (137756686926524073543/50000000000000000000)
  directionHi := (275513373853048147087/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree087.table
  base := (-1644919552599456410607643860379727551223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-8742623808942644998837279253200000000000000)
      constant := (255544079603499559974433560794783216701493008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree087.table
  base := (-6579678246035308041216457850987329076829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-13236869877245977561927570304400000000000000)
      constant := (390663940158816186720294160143798848316095394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137756686926524073543/50000000000000000000)
  centralHi := (275513373853048147087/100000000000000000000)
  directionLo := (27711056621220044837/10000000000000000000)
  directionHi := (277110566212200448371/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree088.table
  base := (-3289977241485724501674354409659330010783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-8841536354554607119032860859200000000000000)
      constant := (261461639052109058122120738246140585825421384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree088.table
  base := (-6579954511705862785497277424391862417601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-40159955196089417746099781637600000000000000)
      constant := (1199126492485732896557560817706999954525657758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27711056621220044837/10000000000000000000)
  centralHi := (277110566212200448371/100000000000000000000)
  directionLo := (278698605380441728369/100000000000000000000)
  directionHi := (27869860538044172837/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree089.table
  base := (-6578658536147048260804914394047905031639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-8940448900166569239228442465200000000000000)
      constant := (267446837072885825836956743434873616198612036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree089.table
  base := (-6578658559312587738630942517789672560107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-40609300760440902806416852362000000000000000)
      constant := (1226571271732503668668611423890183816072154506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278698605380441728369/100000000000000000000)
  centralHi := (27869860538044172837/10000000000000000000)
  directionLo := (70069411735596170489/25000000000000000000)
  directionHi := (280277646942384681957/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree090.table
  base := (-1315158091104263903360411896808691691501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1352000000000000000000000000000000000000000
      center := (2275)
      previous := (0)
      next := (1105)
      square := (14695578205205800714772124320000000000000)
      linear := (-1807872289155706271884804814240000000000000)
      constant := (54699934721593299310797527610757324416545324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree090.table
  base := (-6575790474194936524275313450456879743701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-13686215441597462622244641028800000000000000)
      constant := (418108719319052752856955695963236723939887186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70069411735596170489/25000000000000000000)
  centralHi := (280277646942384681957/100000000000000000000)
  directionLo := (281847842124286791233/100000000000000000000)
  directionHi := (140923921062143395617/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree091.table
  base := (-657135032423821123226273448432598638557/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 104000000000000000000000000000000000000000
      center := (175)
      previous := (0)
      next := (85)
      square := (1130429092708138516520932640000000000000)
      linear := (-140588830636776822763378548880000000000000)
      constant := (4301848440017627094055842323013009741590072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree091.table
  base := (-3285675169644540379070487599553505142993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (3975)
      previous := (0)
      next := (1875)
      square := (25434654585933116621720984400000000000000)
      linear := (-3192922453011067148234691831600000000000000)
      constant := (98645473146723448631487400785108959593079276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281847842124286791233/100000000000000000000)
  centralHi := (140923921062143395617/50000000000000000000)
  directionLo := (7085233449077107957/2500000000000000000)
  directionHi := (283409337963084318281/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree092.table
  base := (-6565338223126551928035065113216050411377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-9237186537002455599815187283200000000000000)
      constant := (285808261997783331435789749275465949921909148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree092.table
  base := (-102583409925875845498049149848286398437/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-41957337453495357987368064535200000000000000)
      constant := (1310766250337872525154867954211936817661097344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7085233449077107957/2500000000000000000)
  centralHi := (283409337963084318281/100000000000000000000)
  directionLo := (284962277467089669031/100000000000000000000)
  directionHi := (35620284683386208629/12500000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree093.table
  base := (-6557754230821687908123791535638782686319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-9336099082614417720010768889200000000000000)
      constant := (292064013744721713418960428541158182904048356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree093.table
  base := (-3278877120297859304998726815512696351733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-14135561005948947682561711753200000000000000)
      constant := (446483818669921585709624536155640251798685476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (284962277467089669031/100000000000000000000)
  centralHi := (35620284683386208629/12500000000000000000)
  directionLo := (286506799768849211989/100000000000000000000)
  directionHi := (28650679976884921199/10000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree094.table
  base := (-6548598423873872191167604972313576689227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-9435011628226379840206350495200000000000000)
      constant := (298387403790212936022542033527716022158082548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree094.table
  base := (-6548598431748949336620281562098480475549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-42856028582198328108002205984000000000000000)
      constant := (1368446767690548386125483306194896422393379942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286506799768849211989/100000000000000000000)
  centralHi := (28650679976884921199/10000000000000000000)
  directionLo := (288043040270623982361/100000000000000000000)
  directionHi := (144021520135311991181/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree095.table
  base := (-3268935438422808043691091915028600282903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-9533924173838341960401932101200000000000000)
      constant := (304778432083852741600828765632131332417515144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree095.table
  base := (-6537870883189969388415900456040615361977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-43305374146549813168319276708400000000000000)
      constant := (1397752185153672825484619998793224448068865966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288043040270623982361/100000000000000000000)
  centralHi := (144021520135311991181/50000000000000000000)
  directionLo := (36196391347865475869/12500000000000000000)
  directionHi := (289571130782923806953/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree096.table
  base := (-3262785831199895398179198364635447319067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-9632836719450304080597513707200000000000000)
      constant := (311237098576521029222897197667012875224621416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree096.table
  base := (-407848229219399744711733689842284485517/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-14584906570300432742878782477600000000000000)
      constant := (475789236059438125278657752027198776506972192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36196391347865475869/12500000000000000000)
  centralHi := (289571130782923806953/100000000000000000000)
  directionLo := (145545599828248000811/50000000000000000000)
  directionHi := (291091199656496001623/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree097.table
  base := (-26046803405519707008234331789744783281/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 270400000000000000000000000000000000000000
      center := (455)
      previous := (0)
      next := (221)
      square := (2939115641041160142954424864000000000000)
      linear := (-389269970602490648031723812528000000000000)
      constant := (12710536128813102892615551531231325265020440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree097.table
  base := (-3255850427748130741647002336999391496537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-44204065275252783288953418157200000000000000)
      constant := (1457293336549141926114506611247795702135068892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145545599828248000811/50000000000000000000)
  centralHi := (291091199656496001623/100000000000000000000)
  directionLo := (292603371908142699527/100000000000000000000)
  directionHi := (36575421488517837441/12500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree098.table
  base := (-3248129256441943112722072263291154702713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-9830661810674228320988676919200000000000000)
      constant := (324357345968562215983133629693030358841932024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree098.table
  base := (-1624064629049759418884421174583038488793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-44653410839604268349270488881600000000000000)
      constant := (1487529070056100899763508176825673587668366776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292603371908142699527/100000000000000000000)
  centralHi := (36575421488517837441/12500000000000000000)
  directionLo := (294107769340715864469/100000000000000000000)
  directionHi := (29410776934071586447/10000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree099.table
  base := (-3239622357165933179778594276696519729689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-9929574356286190441184258525200000000000000)
      constant := (331018926775648906957435257513156305325460472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree099.table
  base := (-1619811179250374451830450444561316784971/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-15034252134651917803195853202000000000000000)
      constant := (506024969498070966786043452619959299120157624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294107769340715864469/100000000000000000000)
  centralHi := (29410776934071586447/10000000000000000000)
  directionLo := (295604510657615948689/100000000000000000000)
  directionHi := (29560451065761594869/10000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree100.table
  base := (-3230329760764757268955377265877234933111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-10028486901898152561379840131200000000000000)
      constant := (337748145597103027607038857036533978370433928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree100.table
  base := (-3230329761839551638865680849851883570381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-45552101968307238469904630330400000000000000)
      constant := (1548930851663388974322356566749501140357801996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree100.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295604510657615948689/100000000000000000000)
  centralHi := (29560451065761594869/10000000000000000000)
  directionLo := (297093711572098804911/100000000000000000000)
  directionHi := (18568356973256175307/6250000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree101.table
  base := (-6440502998726797137896111602195503309517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-10127399447510114681575421737200000000000000)
      constant := (344545002389491600660827930324165839762766508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree101.table
  base := (-6440503000457475811443655084776847350519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-46001447532658723530221701054800000000000000)
      constant := (1580096899368254780369718485422208830359721202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree101.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297093711572098804911/100000000000000000000)
  centralHi := (18568356973256175307/6250000000000000000)
  directionLo := (59715096982335142047/20000000000000000000)
  directionHi := (74643871227918927559/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree102.table
  base := (-6418775208673149401045446842617685234481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-10226311993122076801771003343200000000000000)
      constant := (351409497110396007895526718911390444781490844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree102.table
  base := (-6418775210066419567615157934115419702507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (17225)
      previous := (0)
      next := (8125)
      square := (110216836539043505360790932400000000000000)
      linear := (-15483597699003402863512923926400000000000000)
      constant := (537191017139328751416020704628006964421657902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree102.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59715096982335142047/20000000000000000000)
  centralHi := (74643871227918927559/25000000000000000000)
  directionLo := (150024970358936535313/50000000000000000000)
  directionHi := (300049940717873070627/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree103.table
  base := (-6395476212669342855142698152649110760143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (11375)
      previous := (0)
      next := (5525)
      square := (73477891026029003573860621600000000000000)
      linear := (-10325224538734038921966584949200000000000000)
      constant := (358341629718376927758353280778059201126143332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree103.table
  base := (-6395476213790877980547993632665435689783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (51675)
      previous := (0)
      next := (24375)
      square := (330650509617130516082372797200000000000000)
      linear := (-46900138661361693650855842503600000000000000)
      constant := (1643359307626154598030240392797931744631680114) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree103.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (150024970358936535313/50000000000000000000)
  centralHi := (300049940717873070627/100000000000000000000)
  directionLo := (301517186341601427473/100000000000000000000)
  directionHi := (150758593170800713737/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree104.table
  base := (-6370606070616433052237214948699330021719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (875)
      previous := (0)
      next := (425)
      square := (5652145463540692582604663200000000000000)
      linear := (-801856698795846234012474350400000000000000)
      constant := (28103184628687788207394019670667634838870612) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree104.table
  base := (-6370606071519146389881377775116838021633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (3975)
      previous := (0)
      next := (1875)
      square := (25434654585933116621720984400000000000000)
      linear := (-3642268017362552208551762556000000000000000)
      constant := (128881205216198432099466986794222659902937878) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree104.checked
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
end ForestUnimodality.Stage170KernelData.Cell338.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell338
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 104 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 104 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 104 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel104.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell338

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel105
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  degreePropagationTail 105 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel106
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  degreePropagationTail 106 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel107
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  degreePropagationTail 107 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel108
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  degreePropagationTail 108 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel109
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  degreePropagationTail 109 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel110
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  degreePropagationTail 110 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel111
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  degreePropagationTail 111 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel112
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  degreePropagationTail 112 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel113
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  degreePropagationTail 113 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel114
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  degreePropagationTail 114 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel115
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  degreePropagationTail 115 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel116
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  degreePropagationTail 116 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel117
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  degreePropagationTail 117 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel118
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  degreePropagationTail 118 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel119
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  degreePropagationTail 119 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel120
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  degreePropagationTail 120 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel121
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  degreePropagationTail 121 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel122
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  degreePropagationTail 122 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel123
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  degreePropagationTail 123 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel124
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  degreePropagationTail 124 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel125
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  degreePropagationTail 125 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel126
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  degreePropagationTail 126 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel127
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  degreePropagationTail 127 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel128
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  degreePropagationTail 128 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel129
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  degreePropagationTail 129 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel130
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  degreePropagationTail 130 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel131
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  degreePropagationTail 131 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell338.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 104 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell338.Kernel349

