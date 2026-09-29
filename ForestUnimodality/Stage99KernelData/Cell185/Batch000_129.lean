import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell185.Parameters
import ForestUnimodality.BinomialMassData.Q35_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q35_52.Batch050_099
import ForestUnimodality.BinomialMassData.Q35_52.Batch100_149
import ForestUnimodality.BinomialMassData.Q53_78.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_78.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_78.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel000
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
  base := (68384706337225260055934229/12500000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-28367000140510977568286677000000000000000)
      constant := (2844803783628570818326863926400000000000000) }

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
  base := (68384706337225260055934229/12500000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (25251624347193743491679640720000000000000)
      linear := (-42550500210766466352430015500000000000000)
      constant := (4267205675442856227490295889600000000000000) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel001
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
  base := (39901131103681965372137254239368063773833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-663373285877236382457322609400000000000000)
      constant := (27320520876758583285599175494312811111111108) }

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
  base := (39762692238613296305284855060521909927679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-2997805598621160592803791562660000000000000)
      constant := (122540389153083287087401361112437649999999518) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel002
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
  base := (7217402149567087188092106417154239603879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-957975569927830056526918417800000000000000)
      constant := (20408857912648760425293605418485063888888816) }

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
  base := (14332459155385696591678476795125170529257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-4336141689022428997862812520820000000000000)
      constant := (91272622443082514253992390073361537499999588) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel003
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
  base := (4125273464244543607172848607533333072561/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-1252577853978423730596514226200000000000000)
      constant := (15580363057795903316218702407462665785256180) }

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
  base := (10199573295127313894580000908666680633787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-1891492593141232467640611159660000000000000)
      constant := (23176396221012489041703947076266028325320036) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel004
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
  base := (14444468071834512811477383840321549991289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-1547180138029017404666110034600000000000000)
      constant := (12343625412519673120438876447057367794111364) }

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
  base := (14220015727419315607559170648976696015349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-7012813869824965807980854437140000000000000)
      constant := (55042698587332057405719564478467109278691658) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel005
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
  base := (1223813473559472360587579133906211315567/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-1841782422079611078735705843000000000000000)
      constant := (10338064507159572802467250193664790794586336) }

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
  base := (1916480993801462278681223466080166985573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-8351149960226234213039875395300000000000000)
      constant := (46154894884555007260074301162329339850565330) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel006
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
  base := (3142601150403032643290360876221882708967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-2136384706130204752805301651400000000000000)
      constant := (9307284242565457507291413818151985422523384) }

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
  base := (6099747470802956942093862042096226764213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-3229828683542500872699632117820000000000000)
      constant := (13896613738200761476587206223145573938911982) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel007
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
  base := (3621201639382934493588006757423055174713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-2430986990180798426874897459800000000000000)
      constant := (9043516039394239469005328567017985298105988) }

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
  base := (3460312013590909197126334230619614628347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-11027822141028771023157917311620000000000000)
      constant := (40699251208620815336920470376214867699431574) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel008
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
  base := (1583242346848543764422607170746411653447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-2725589274231392100944493268200000000000000)
      constant := (9401241800472016994490274941424574277730172) }

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
  base := (451976774413934409769429471457115161/3125000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-12366158231430039428216938269780000000000000)
      constant := (42520659646262509561842640418072141823238400) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel009
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
  base := (12063048713324042785698311303850014369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-3020191558281985775014089076600000000000000)
      constant := (10272800836643841401688247456941402609713444) }

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
  base := (-51398273053767768910237093519506051961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-4568164773943769277758653075980000000000000)
      constant := (15555188975183758986075013811252441726623092) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel010
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
  base := (-605121985614061748139722730843248554103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-3314793842332579449083684885000000000000000)
      constant := (11578487531754863084928499580399927954852744) }

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
  base := (-1305552926774152819018120540664310610619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-15042830412232576238334980186100000000000000)
      constant := (52773501316238977546484492180799167122497002) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel011
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
  base := (-1085523426939613150015563410950804160689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-3609396126383173123153280693400000000000000)
      constant := (13259241022554365089864418704394512774748472) }

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
  base := (-28118305604626582376599617647405859549/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-16381166502633844643394001144260000000000000)
      constant := (60578223983492232429201896084757310020155360) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel012
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
  base := (-366893563249552964722776224525131232743/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-3903998410433766797222876501800000000000000)
      constant := (15271254544074994416360508746768090293325856) }

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
  base := (-1499619530233521406872567252561993909773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-5906500864345037682817674034140000000000000)
      constant := (23294297781571425702720972418644276350980356) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel013
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
  base := (-1775333336465289109235883333056121701129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-322969284191104651637882485400000000000000)
      constant := (1352461576958428310416458218862163343082584) }

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
  base := (-3602771534614075607133562180146159596701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2703)
      previous := (0)
      next := (1275)
      square := (75754873041581230475038922160000000000000)
      linear := (-1465987591033567804116311004660000000000000)
      constant := (6195524115757886455280817759135798654371966) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel014
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
  base := (-4053371387945660605023988015355081224459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-4493202978534954145362068118600000000000000)
      constant := (20167298349221641684248010165119965092265716) }

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
  base := (-1023888632060674888052985908681695472497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-20396174773837649858571064018740000000000000)
      constant := (92447015800000427182468378299341129490656504) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel015
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
  base := (-2234943176397228440485167303796232681699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-4787805262585547819431663927000000000000000)
      constant := (23009150467976332024475401230267493414342952) }

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
  base := (-4503923547009632117102264111423272805311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-7244836954746306087876694992300000000000000)
      constant := (35172795873983417453863026813266801375414646) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel016
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
  base := (-964010692921681112503049194537962587623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-5082407546636141493501259735400000000000000)
      constant := (26094143734262786619141928918461686453834260) }

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
  base := (-302965363496381248813848657942195072921/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-23072846954640186668689105935060000000000000)
      constant := (119696405472169175897834456233117481410789088) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel017
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
  base := (-2559340312848359626137735756033216652501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-5377009830686735167570855543800000000000000)
      constant := (29412268006119977748878670634343091085818648) }

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
  base := (-128517008945059523525765847001118910513/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-24411183045041455073748126893220000000000000)
      constant := (134936780803414348732545713310273850968778160) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel018
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
  base := (-5376834807377468754797164466875734204929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-5671612114737328841640451352200000000000000)
      constant := (32956042010936889549812426786892003677467996) }

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
  base := (-2697237976456696721786797645250636093341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-8583173045147574492935715950460000000000000)
      constant := (50402170541981150983879900458571710002704452) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel019
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
  base := (-5602799579105580295263786287458166872537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-5966214398787922515710047160600000000000000)
      constant := (36719866055761991893719177435678279194164988) }

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
  base := (-5616929241253351473187229553590047780729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-27087855225843991883866168809540000000000000)
      constant := (168480967960942761614155575838609074651022382) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel020
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
  base := (-5802784881665719887198397052139243229381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-6260816682838516189779642969000000000000000)
      constant := (40699542220624850555457333967753871576938444) }

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
  base := (-2907046345538724827295848716148616039853/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-28426191316245260288925189767700000000000000)
      constant := (186741738199979972671694607657951820013534348) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel021
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
  base := (-5981453713177327154913844940089444126567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-6555418966889109863849238777400000000000000)
      constant := (44891918318796724348991411013999535770440708) }

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
  base := (-2995249158777443851774862170319494331603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-9921509135548842897994736908620000000000000)
      constant := (68658345317636793529635528708102065495509116) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel022
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
  base := (-76778917500026915647767112975691892337/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-6850021250939703537918834585800000000000000)
      constant := (49294623397657069494615410951774582462415040) }

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
  base := (-6149545559720559096270044593429847644421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-31102863497047797099043231684020000000000000)
      constant := (226170520126189839411164541452006403465671318) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel023
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
  base := (-6288006618869620394545939681573612716027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-7144623534990297211988430394200000000000000)
      constant := (53905871007736796573890853834256237803965748) }

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
  base := (-3146894454528408754356589966745818355069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-32441199587449065504102252642180000000000000)
      constant := (247320419956729029256196566499388441127760204) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel024
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
  base := (-3210264065237225462825628741520211717931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-7439225819040890886058026202600000000000000)
      constant := (58724312690806273283244678047464673757357288) }

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
  base := (-3212575740283862636247510000948822224371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-11259845225950111303053757866780000000000000)
      constant := (89806295109561864170409041659435788528975612) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel025
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
  base := (-6541386404007415959627365474355777271349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-7733828103091484560127622011000000000000000)
      constant := (63748928721692538349281614501835494564568076) }

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
  base := (-6545083814507625067439637469625164921949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-35117871768251602314220294558500000000000000)
      constant := (292461503698605818744231387823650248307431142) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel026
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
  base := (-207866384829571113554076107267516435791/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-617571568241698325707478293800000000000000)
      constant := (5306072808987925070708960852006852650843776) }

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
  base := (-6654682126114486802233758623021671621649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2703)
      previous := (0)
      next := (1275)
      square := (75754873041581230475038922160000000000000)
      linear := (-2804323681434836209175331962820000000000000)
      constant := (24341918490748907960998794897872928840534134) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel027
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
  base := (-6752409409502420031309424312237960947473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-8323032671192671908266813627800000000000000)
      constant := (74413779614207636296705412868927138399508252) }

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
  base := (-3377388246496749209552321269760116202889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-12598181316351379708112778824940000000000000)
      constant := (113788890092000188345743546803616484340541108) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel028
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
  base := (-3422050760035226306209836229040669206577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-8617634955243265582336409436200000000000000)
      constant := (80052981967898817542750969807337015232707896) }

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
  base := (-1369199345472236567221022670948771140187/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-39132880039455407529397357432980000000000000)
      constant := (367224777498637440660253617018589190957755730) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel029
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
  base := (-865912935546816812191917457478784464229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-8912237239293859256406005244600000000000000)
      constant := (85896213659344636739912629873454733617449568) }

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
  base := (-3464410830561211524988933343351821573641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-40471216129856675934456378391140000000000000)
      constant := (394017805440991776285961983425577517545968156) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel030
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
  base := (-3501199631830318271434714672869007157917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-9206839523344452930475601053000000000000000)
      constant := (91943215130742817589390402749781102322496216) }

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
  base := (-280144643347631551264079654267889156623/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-13936517406752648113171799783100000000000000)
      constant := (140581548137889164274480517145809009879606950) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel031
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
  base := (-7069682633848130986556726611366079594959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-9501441807395046604545196861400000000000000)
      constant := (98193787789571864458205173711716530193807716) }

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
  base := (-883832309351586445324588027691409162479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-43147888310659212744574420307460000000000000)
      constant := (450404447281276006393506663375731866621911056) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel032
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
  base := (-7129378820772166494868301928680406718369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-9796044091445640278614792669800000000000000)
      constant := (104647779383167216847957699120212045058382556) }

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
  base := (-7130161864173672333043214442579712995443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-44486224401060481149633441265620000000000000)
      constant := (479996566007513901456430280971592513067862394) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel033
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
  base := (-1795415210991931644534190632988900159171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-10090646375496233952684388478200000000000000)
      constant := (111305072950323225905663136484898013969601616) }

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
  base := (-7182289550480333016934129738612634576397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-15274853497153916518230820741260000000000000)
      constant := (170173501279238564986475630514836788539533442) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel034
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
  base := (-3613330942971151636322728113791528977909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-10385248659546827626753984286600000000000000)
      constant := (118165578459664827014793942688653852821867032) }

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
  base := (-289086678775257011874034309350529089441/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-47162896581863017959751483181940000000000000)
      constant := (541975879196637884284083853101872262748011950) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel035
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
  base := (-1452896934213060126203757274591536504191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-10679850943597421300823580095000000000000000)
      constant := (125229226469518303035776021061880606615834420) }

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
  base := (-3632445335563218044761816633925791023223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-48501232672264286364810504140100000000000000)
      constant := (574362398378421530229707791260945487414711268) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel036
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
  base := (-7295208590596554553603864573636205477683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-10974453227648014974893175903400000000000000)
      constant := (132495963311392004899974724159221925097086292) }

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
  base := (-3647767562594289913482845642786981691283/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-16613189587555184923289841699420000000000000)
      constant := (202559944948976371498038148439988001130078076) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel037
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
  base := (-7318895125929156632620500514799636509959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-11269055511698608648962771711800000000000000)
      constant := (139965747423864202691049460633495445719267716) }

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
  base := (-7319157888069020316105424358238957684343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-51177904853066823174928546056420000000000000)
      constant := (641928013515284096776627645077007090724228594) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel038
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
  base := (-3667795992268445880624053772281697629069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-11563657795749202323032367520200000000000000)
      constant := (147638546556682617821210947061375144805498712) }

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
  base := (-733580353584691446000177074124544174557/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-52516240943468091579987567014580000000000000)
      constant := (677106798783053681778142100359151366209976060) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel039
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
  base := (-3672668130171085893022305877884437720761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-912173852292291999777074102200000000000000)
      constant := (11962641202642746144783540415700018477040856) }

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
  base := (-918188332840596137307261276615793108277/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (25251624347193743491679640720000000000000)
      linear := (-1380886590612034871411450973660000000000000)
      constant := (18287591933709585735691692069761745100435152) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel040
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
  base := (-3674078426667539597600703704046397135399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-12152862363850389671171559137000000000000000)
      constant := (163593095120490153111957313142129271072940552) }

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
  base := (-1837073542992235204318768859030386552411/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-55192913124270628390105608930900000000000000)
      constant := (750255791570408325784123609081318256430262952) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel041
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
  base := (-7344076325667548668475394645233305109593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-12447464647900983345241154945400000000000000)
      constant := (171874809763071269667009145778322285745915132) }

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
  base := (-3672093514853227865082940176055915702311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-56531249214671896795164629889060000000000000)
      constant := (788225853471298714616669541151605808867139876) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel042
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
  base := (-366655616410770759060282929148261308343/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-12742066931951577019310750753800000000000000)
      constant := (180359467630106985104012301774415507111202640) }

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
  base := (-3666600805081938428198399261846506547993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-19289861768357721733407883615740000000000000)
      constant := (275708740435649268495001907304515284720670196) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel043
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
  base := (-7315278699103818210167512810939837967581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-13036669216002170693380346562200000000000000)
      constant := (189047059367024705136666669143804669533915244) }

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
  base := (-1463070145906387436926578463279355597803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-59207921395474433605282671805380000000000000)
      constant := (866956856090503388637613031651191001357416370) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel044
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
  base := (-7290586311221113960135144081865442515993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-13331271500052764367449942370600000000000000)
      constant := (197937577623751900970544897641658960859188732) }

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
  base := (-7290644442049586186072365434784741457751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-60546257485875702010341692763540000000000000)
      constant := (907717727236970579783106534695264816485521458) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel045
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
  base := (-7259043727287787950310507094827991710287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-13625873784103358041519538179000000000000000)
      constant := (207031016611889524394666465891396277603845988) }

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
  base := (-907386331768387807323629287592043058933/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-20628197858758990138466904573900000000000000)
      constant := (316469603564996157142251360496803346705935504) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel046
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
  base := (-3610328853548878681780819972613193864281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-13920476068153951715589133987400000000000000)
      constant := (216327371761816887393412580140526961895492088) }

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
  base := (-7220695599101123086677772450898782093639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-63222929666678238820459734679860000000000000)
      constant := (992030087502929533557522266738145904871150162) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel047
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
  base := (-179385840024717357531750088648382180109/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-14215078352204545389658729795800000000000000)
      constant := (225826639456705723626249372811947745849852640) }

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
  base := (-3587732102270631405661315379310375821379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-64561265757079507225518755638020000000000000)
      constant := (1035581542670944478133337607681745673502730164) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel048
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
  base := (-1424675131117496082518914399518376479963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-14509680636255139063728325604200000000000000)
      constant := (235528816825836261098345377413627887497725060) }

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
  base := (-1424680075498611552386418766794981102761/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-21966533949160258543525925532060000000000000)
      constant := (360021054771287208082846498045789445809001730) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel049
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
  base := (-3532243625894593147447359150835607308531/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-14804282920305732737797921412600000000000000)
      constant := (245433901583723432085885657796570258918866088) }

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
  base := (-706450722583634077148645668750448264323/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-67237937937882044035636797554340000000000000)
      constant := (1125474942977510520425201868682941363799294340) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel050
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
  base := (-6998771090292598462400468577487696809883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-15098885204356326411867517221000000000000000)
      constant := (255541891904694856905250716304118316956519092) }

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
  base := (-3499393615323171767535562462555840905553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-68576274028283312440695818512500000000000000)
      constant := (1171816871114460311846874927465310263930615548) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel051
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
  base := (-3463114668239481013041775622240854960131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-15393487488406920085937113029400000000000000)
      constant := (265852786324952813861423664524730364093902888) }

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
  base := (-6926242380525522437363375992911785926949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-23304870039561526948584946490220000000000000)
      constant := (406362980891794108730456797497797449070073714) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel052
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
  base := (-136937274674349119110542549591073360563/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-1206776136342885673846669910600000000000000)
      constant := (21258967974306133690074329654063209262536200) }

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
  base := (-6846874276471131254750369431275352680659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2703)
      previous := (0)
      next := (1275)
      square := (75754873041581230475038922160000000000000)
      linear := (-5480995862237373019293373879140000000000000)
      constant := (97483934830003301343916809572721567472725794) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel053
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
  base := (-6760675692110649363216157224432680164321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-15982692056508107434076304646200000000000000)
      constant := (287083282974546292513838746317783508208919004) }

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
  base := (-6760684213864266709354963422531667759517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-72591282299487117655872881386980000000000000)
      constant := (1316423497517892789456821588730628666675549286) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel054
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
  base := (-3333833179052283478303756106293001945149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-16277294340558701108145900454600000000000000)
      constant := (298002883475654964787800201677791861370158552) }

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
  base := (-6667673246665355402054305160337068192183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-24643206129962795353643967448380000000000000)
      constant := (455495324550928108143070434528678212853126438) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel055
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
  base := (-3283918334583316998891815794454065034893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-16571896624609294782215496263000000000000000)
      constant := (309125384535577775315682922720898104072824664) }

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
  base := (-656784223774928318317402958615331435611/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-75267954480289654465990923303300000000000000)
      constant := (1417478578569852119631397087519671617728713380) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel056
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
  base := (-258447495871759973248341735039107278871/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-16866498908659888456285092071400000000000000)
      constant := (320450785632782651478629226503839086987080100) }

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
  base := (-3230595949213871101183949294520567718131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-76606290570690922871049944261460000000000000)
      constant := (1469401310105286007544132196865016866002890996) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel057
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
  base := (-3173859590194372576875036977917382397379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-17161101192710482130354687879800000000000000)
      constant := (331979086335033785711556462392355698998743592) }

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
  base := (-1269544563904821812775202483592068344963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-25981542220364063758702988406540000000000000)
      constant := (507418055487267092179106082221578213491037590) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel058
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
  base := (-1556858138493807595110819623222647740841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-17455703476761075804424283688200000000000000)
      constant := (343710286281330711387900933095305960508765936) }

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
  base := (-6227435495839606439940197915995768652007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-79282962751493459681167986177780000000000000)
      constant := (1576037146134212607241995599662160871760594706) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel059
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
  base := (-6100327967300133720116622982638894635337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-17750305760811669478493879496600000000000000)
      constant := (355644385167644673700494595599736107226512188) }

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
  base := (-6100330345442380413438318251681993198167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-80621298841894728086227007135940000000000000)
      constant := (1630750247850756699274049796098613376691175986) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel060
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
  base := (-5966405802518533927696325155771227576917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-18044908044862263152563475305000000000000000)
      constant := (367781382735638839411007326719698650158004108) }

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
  base := (-1193281544979161450847150680820871025481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-27319878310765332163762009364700000000000000)
      constant := (562131156842255920673516783359238183900811330) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel061
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
  base := (-728208298425912761740365478421641667021/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-18339510328912856826633071113400000000000000)
      constant := (380121278763736043662098522216195761864750432) }

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
  base := (-5825667941297715861758273219657030155103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-83297971022697264896345049052260000000000000)
      constant := (1742966813228054199969444069726733314268176674) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel062
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
  base := (-1419527501460775158349940942852966733553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-18634112612963450500702666921800000000000000)
      constant := (392664073060035662661496321022025577952472688) }

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
  base := (-1419527815453030053826367841009134201593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-84636307113098533301404070010420000000000000)
      constant := (1800470275141903082595701591114620855035016376) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel063
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
  base := (-172616778316352032123442498664528139467/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-18928714897014044174772262730200000000000000)
      constant := (405409765456688697623488162217888927287049856) }

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
  base := (-5523737921227112101011260878080773475459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-28658214401166600568821030322860000000000000)
      constant := (619634618518029678228634516923716095695884574) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel064
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
  base := (-670318413447961376595251291533645450281/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-19223317181064637848841858538600000000000000)
      constant := (418358355805424083031087026791386045404880352) }

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
  base := (-134063703198931277495114553079040096859/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-87312979293901070111522111926740000000000000)
      constant := (1918267553830614965994864112117022401014196880) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel065
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
  base := (-2597270702935389077585189468894734055259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-1501378420393479347916265719000000000000000)
      constant := (33193064921075757905905723957734947658253064) }

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
  base := (-5194542068818780917222516614588878990861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2703)
      previous := (0)
      next := (1275)
      square := (75754873041581230475038922160000000000000)
      linear := (-6819331952638641424352394837300000000000000)
      constant := (152197028415629681782333805629436202316138526) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel066
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
  base := (-1003943875429695806396033568017393036011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-19812521749165825196981050155400000000000000)
      constant := (444864229843284174918630202398601211538282820) }

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
  base := (-501971991283564968255368776702162824971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-29996550491567868973880051281020000000000000)
      constant := (679928433919210292001011213846900068954794060) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel067
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
  base := (-967616276292384012008696403976926834603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-20107124033216418871050645963800000000000000)
      constant := (458421513305131543998862376668557987299041860) }

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
  base := (-302380113392453302471639615420541269937/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-91327987565104875326699174801220000000000000)
      constant := (2101939350424656419553064780585121415309626336) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel068
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
  base := (-185985102617291609679492037987052644983/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-20401726317267012545120241772200000000000000)
      constant := (472181694260411036251695096137018810299787300) }

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
  base := (-2324813957550836712863682987266440496591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-92666323655506143731758195759380000000000000)
      constant := (2165023514972444257220275114086390976018740356) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel069
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
  base := (-4454358064420938544274596700470406679669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-20696328601317606219189837580600000000000000)
      constant := (486144772617618379775799391683982005084543756) }

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
  base := (-4454358346888347806628336795136950810751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-31334886581969137378939072239180000000000000)
      constant := (743012598333570497193572857166441131877898486) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel070
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
  base := (-2126136502135851261608507992259575363929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-20990930885368199893259433389000000000000000)
      constant := (500310748291683140383108590131965054107967992) }

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
  base := (-531534154053687800499791434373637772447/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-95342995836308680541876237675700000000000000)
      constant := (2293982190135930253859434131547583151169729808) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel071
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
  base := (-1010843125679428655171901096940570129637/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-21285533169418793567329029197400000000000000)
      constant := (514679621203017720542916512664872698369461552) }

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
  base := (-4043372686988807643305363124713579100383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-96681331926709948946935258633860000000000000)
      constant := (2359856700027468458622148098348651292376634914) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel072
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
  base := (-382765667052097558246036534727998166887/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-21580135453469387241398625005800000000000000)
      constant := (529251391276747007751079932959238732391843880) }

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
  base := (-765531363866249568066426821667779464241/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-32673222672370405783998093197340000000000000)
      constant := (808887108114821007860083163770384358116298130) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel073
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
  base := (-901281403099703344796646590182342968003/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-21874737737519980915468220814200000000000000)
      constant := (544026058442082088299438580666646944614519888) }

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
  base := (-3605125732559249541977798980695370239191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-99358004107512485757053300550180000000000000)
      constant := (2494396062773276367178071082279294683732380978) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel074
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
  base := (-421972428472519053682349151118097368187/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-22169340021570574589537816622600000000000000)
      constant := (559003622631809009281023908359253329432844704) }

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
  base := (-675155904959179138745044335806108521261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-100696340197913754162112321508340000000000000)
      constant := (2563060915015418071095453999155969089391620190) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel075
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
  base := (-3139618211425668555864609100141514545667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-22463942305621168263607412431000000000000000)
      constant := (574184083781869553839766682748304336167129108) }

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
  base := (-1569809144872996077926490935762927558899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-34011558762771674189057114155500000000000000)
      constant := (877551960261946038635143600863522782910552828) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel076
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
  base := (-2896642053938903225646526295207178622931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-22758544589671761937677008239400000000000000)
      constant := (589567441831015727943810979065439947250898644) }

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
  base := (-2896642117159387041893016824770023014423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-103373012378716290972230363424660000000000000)
      constant := (2703180959811517463646637339418129589990125234) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel077
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
  base := (-1323425521094933078441101266914469193137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-23053146873722355611746604047800000000000000)
      constant := (605153696720523405023736300678631637650878776) }

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
  base := (-2646851093215911861735082099024944005663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-104711348469117559377289384382820000000000000)
      constant := (2774636151830297066865988973224336120334773154) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel078
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
  base := (-2390245259668261626344305661089748777459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-1795980704444073021985861527400000000000000)
      constant := (47764834491842580383726486471123333063572132) }

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
  base := (-597561325211833442297126845600999448531/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (25251624347193743491679640720000000000000)
      linear := (-2719222681013303276470471931820000000000000)
      constant := (73000550168971756150810198028152488172058328) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel079
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
  base := (-265853098347498677693519026085938966837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-23642351441823542959885795664600000000000000)
      constant := (636934896796951759581574695427927242067345504) }

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
  base := (-2126824820008558181973040220408770822489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-107388020649920096187407426299140000000000000)
      constant := (2920336873847098910412760117005546519157988462) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel080
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
  base := (-1856589701097806169709653983355604808589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-23936953725874136633955391473000000000000000)
      constant := (653129841877078865323129458207251611149393836) }

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
  base := (-1856589727907825937656168636486409743653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-108726356740321364592466447257300000000000000)
      constant := (2994582403367030859831595856379808341559807574) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel081
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
  base := (-789770038787418391657475840324455301391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-24231556009924730308024987281400000000000000)
      constant := (669527683583666549772267981352381336432519368) }

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
  base := (-789770049601835713424113566329365951213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-36688230943574210999175156071820000000000000)
      constant := (1023252681640861025507289434555194045850940036) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel082
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
  base := (-1295675988727880614278618051941818802169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-24526158293975323982094583089800000000000000)
      constant := (686128421867693456567096013683387330489733756) }

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
  base := (-1295676006174839432714238865218202703361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-111403028921123901402584489173620000000000000)
      constant := (3145863798293883618853189458421426227376375838) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel083
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
  base := (-1004997504796069094131625895006986161289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-24820760578025917656164178898200000000000000)
      constant := (702932056681677932859898617588975277354968636) }

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
  base := (-251249379717028311550091891744205383903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-112741365011525169807643510131780000000000000)
      constant := (3222899663267850172054501090572126508888668296) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel084
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
  base := (-353752346939663612135381919846082698839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-25115362862076511330233774706600000000000000)
      constant := (719938587979584429349731563955368096191169672) }

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
  base := (-70750470522801757997663492920784436719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-38026567033975479404234177029980000000000000)
      constant := (1100288546545931830649953664710943245811669340) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel085
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
  base := (-201598811030105886016277546261196344149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-25409965146127105004303370515000000000000000)
      constant := (737148015716741137661875363094954862542710552) }

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
  base := (-100799407802893402947301036891095936271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-115418037192327706617761552048100000000000000)
      constant := (3379761727203078320116565340662359144647454472) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel086
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
  base := (-92076353511998110114433592554926060277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-25704567430177698678372966323400000000000000)
      constant := (754560339849766923644386549664932869983252748) }

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
  base := (-23019090222664515180800539881237028603/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-116756373282728975022820573006260000000000000)
      constant := (3459587925768792007575157174016905107835958696) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel087
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
  base := (14116190587791961658894996653930557889/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-25999169714228292352442562131800000000000000)
      constant := (772175560336505993051804817902808912914127424) }

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
  base := (225859043455979745185081011949789626869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-39364903124376747809293197988140000000000000)
      constant := (1180114745048494866289916699982207086681645166) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel088
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
  base := (550608526054710692428303631999605827039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-26293771998278886026512157940200000000000000)
      constant := (789993677135969027730885812129231733539078364) }

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
  base := (27530426062969282489165137109352081699/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-119433045463531511832938614922580000000000000)
      constant := (3622030655148905335457328692187252980650567160) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel089
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
  base := (55135751090598439474870848714061267149/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-26588374282329479700581753748600000000000000)
      constant := (808014690208279771413090317638191286665483584) }

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
  base := (44108600679220631951790768186240007681/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-120771381553932780237997635880740000000000000)
      constant := (3704647185599773500121196510534380842067312040) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel090
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
  base := (610274733087541105052905520977543251197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-26882976566380073374651349557000000000000000)
      constant := (826238599514626236935311244876861638475618344) }

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
  base := (305137365764997265394585261702801785011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-40703239214778016214352218946300000000000000)
      constant := (1262731275441188764299301140609966564040004616) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel091
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
  base := (62629632653002939358037172508182137713/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-2090582988494666696055457335800000000000000)
      constant := (64974261924401220075892608716260636779026900) }

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
  base := (1565740813814757188819715299381066978311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2703)
      previous := (0)
      next := (1275)
      square := (75754873041581230475038922160000000000000)
      linear := (-9496004133441178234470436753620000000000000)
      constant := (297897736703871003352082700283765169672924774) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel092
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
  base := (1917746013440099977208898367094815047671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-27472181134481260722790541173800000000000000)
      constant := (863295106679234056126843435285156094972225596) }

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
  base := (29964781428396217495000555428853584821/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-124786389825136585453174698755220000000000000)
      constant := (3958077437914463557773226492481452646721630848) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel093
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
  base := (1138282502225233727612920244746352677043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-27766783418531854396860136982200000000000000)
      constant := (882127704464805709053403789462397068819362136) }

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
  base := (1138282501410383536257584016416126382057/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-42041575305179284619411239904460000000000000)
      constant := (1348138136151539595975265377771681904302811596) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel094
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
  base := (2642197737623090232636424645536839863057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-28061385702582448070929732790600000000000000)
      constant := (901163198338959253842978012063882903747426532) }

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
  base := (1321098868155096400533147282059412752797/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-127463062005939122263292740671540000000000000)
      constant := (4131681488613472337238464701251429467188016948) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel095
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
  base := (1507322081255849984343079427130088875941/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-28355987986633041744999328599000000000000000)
      constant := (920401588267593013097216066510479880160272232) }

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
  base := (602928832290825482359249426371564090003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-128801398096340390668351761629700000000000000)
      constant := (4219878678237611559307492131205861489808945630) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel096
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
  base := (678780845982006340044090077105300990339/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-28650590270683635419068924407400000000000000)
      constant := (939842874217443551701025448116615917347345820) }

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
  base := (3393904229058214369256937626689112049293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-43379911395580553024470260862620000000000000)
      constant := (1436335325725795740517348446383222759617983102) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel097
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
  base := (3779977891807671370880975501744880728921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-28945192554734229093138520215800000000000000)
      constant := (959487056156055829752307930035679539372750596) }

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
  base := (1889988945560822915351317945231485822659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-131478070277142927478469803546020000000000000)
      constant := (4399063385286780866514491813941758359745057356) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel098
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
  base := (521608137668537408713211832352723385393/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-29239794838784822767208116024200000000000000)
      constant := (979334134051754975126453173535863528068205344) }

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
  base := (2086432550397925128226816998260727130413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-132816406367544195883528824504180000000000000)
      constant := (4490050902423279139571125884069238263861432692) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel099
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
  base := (2286282906395052266942322063384803638687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-29534397122835416441277711832600000000000000)
      constant := (999384107873619523680201643135696254519504824) }

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
  base := (1143141453086316392800912299961350163641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-44718247485981821429529281820780000000000000)
      constant := (1527322842815918153629621945807253236263727896) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel100
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
  base := (4979079981468179065439978554601557879543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-29828999406886010115347307641000000000000000)
      constant := (1019636977591455997539320315377910653126571068) }

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
  base := (4979079981110022653371427853383255027887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-135493078548346732693646866420500000000000000)
      constant := (4674816263224351508599861500404991861794832254) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel101
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
  base := (1348101890939681587363432451070558084101/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-30123601690936603789416903449400000000000000)
      constant := (1040092743175774710259724643801194789059409104) }

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
  base := (215696302538815516745832926550332644359/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-136831414638748001098705887378660000000000000)
      constant := (4768594106620379053140638364473482797603501950) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel102
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
  base := (1453137129261235732778678691834698459773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-30418203974987197463486499257800000000000000)
      constant := (1060751404597766702705962268624221024635226192) }

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
  base := (5812548516812833486988557308899283893887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-46056583576383089834588302778940000000000000)
      constant := (1621100686168735580900039996164163873868401418) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel103
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
  base := (623950279968444866017651824350233560063/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-30712806259037791137556095066200000000000000)
      constant := (1081612961829281725896466613171607578866025880) }

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
  base := (3119751399748809857225457618720427058593/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-139508086819550537908823929294980000000000000)
      constant := (4958940118755166489281414381275765078224479812) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel104
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
  base := (3336635185489078501775154656555739561087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-2385185272545260370125053144200000000000000)
      constant := (84821339603292861333451509826281796914353048) }

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
  base := (6673270370827788398309878688823783410979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2340000000000000000000000000000000000000000
      center := (2703)
      previous := (0)
      next := (1275)
      square := (75754873041581230475038922160000000000000)
      linear := (-10834340223842446639529457711780000000000000)
      constant := (388885252864881395848602932405744765318169086) }

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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301517186341601427473/100000000000000000000)
  centralHi := (150758593170800713737/50000000000000000000)
  directionLo := (9468041454198989737/3125000000000000000)
  directionHi := (60595465306873534317/20000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree105.table
  base := (7113851191140489366982560915031362472411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-31302010827138978485695286683000000000000000)
      constant := (1123944763611448065891455928041061201031349836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree105.table
  base := (7113851191019476258199306719111395406743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-47394919666784358239647323737100000000000000)
      constant := (1717668854616686400284172469245928954942437402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9468041454198989737/3125000000000000000)
  centralHi := (60595465306873534317/20000000000000000000)
  directionLo := (304430463535549784693/100000000000000000000)
  directionHi := (152215231767774892347/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree106.table
  base := (7561245221270847941214607749571686106193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-31596613111189572159764882491400000000000000)
      constant := (1145415008108907527447166656327210459807786468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree106.table
  base := (7561245221173467782271402756895353186929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-143523095090754343124000992169460000000000000)
      constant := (5251434948456638240156411243494855664394638018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304430463535549784693/100000000000000000000)
  centralHi := (152215231767774892347/50000000000000000000)
  directionLo := (76469174288984970651/25000000000000000000)
  directionHi := (61175339431187976521/20000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree107.table
  base := (160309048466525409721464533142753182811/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-31891215395240165833834478299800000000000000)
      constant := (1167088148309468539527644713744225057579011800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree107.table
  base := (4007726211623957273013995569699073576737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-144861431181155611529060013127620000000000000)
      constant := (5350793440947471961036196178179719163640867908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76469174288984970651/25000000000000000000)
  centralHi := (61175339431187976521/20000000000000000000)
  directionLo := (61463224971549748911/20000000000000000000)
  directionHi := (76829031214437186139/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree108.table
  base := (1695294552019039600004955420335493614107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-32185817679290759507904074108200000000000000)
      constant := (1188964184187976088247853359289733968415681660) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree108.table
  base := (8476472760032154934819426594561687133821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-48733255757185626644706344695260000000000000)
      constant := (1817027347069788510286702663624925550753694494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61463224971549748911/20000000000000000000)
  centralHi := (76829031214437186139/25000000000000000000)
  directionLo := (19296802614453331511/6250000000000000000)
  directionHi := (308748841831253304177/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree109.table
  base := (8944306195172292643440843850572998450177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-32480419963341353181973669916600000000000000)
      constant := (1211043115719820165228203784266487346952319652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree109.table
  base := (1788861239024314809485231818867389236977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-147538103361958148339178055043940000000000000)
      constant := (5552300749131576111098636810394702990294420170) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19296802614453331511/6250000000000000000)
  centralHi := (308748841831253304177/100000000000000000000)
  directionLo := (310174941068257679661/100000000000000000000)
  directionHi := (155087470534128839831/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree110.table
  base := (9418952692934248792825333269242847655619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-32775022247391946856043265725000000000000000)
      constant := (1233324942880919415867212629377508165015198444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree110.table
  base := (4709476346446724301570438315304684464227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-148876439452359416744237076002100000000000000)
      constant := (5654449564605739377531870993610813700280357068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310174941068257679661/100000000000000000000)
  centralHi := (155087470534128839831/50000000000000000000)
  directionLo := (155797256716264085573/50000000000000000000)
  directionHi := (311594513432528171147/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree111.table
  base := (9900412218516544862660496921327821352943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-33069624531442540530112861533400000000000000)
      constant := (1255809665647705423573069896679817607234589468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree111.table
  base := (1237551527310465757417687003686719228049/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-50071591847586895049765365653420000000000000)
      constant := (1919176162508599627441718054502716666377933488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155797256716264085573/50000000000000000000)
  centralHi := (311594513432528171147/100000000000000000000)
  directionLo := (62601529545470638839/20000000000000000000)
  directionHi := (78251911931838298549/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree112.table
  base := (5194342368895543836077032370116849150161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-33364226815493134204182457341800000000000000)
      constant := (1278497283997107597355560011608397980051017672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree112.table
  base := (2597171184441172746101043254493746991193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-151553111633161953554355117918420000000000000)
      constant := (5861537517787938115135486585808199913388836424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62601529545470638839/20000000000000000000)
  centralHi := (78251911931838298549/25000000000000000000)
  directionLo := (39301803845046287119/12500000000000000000)
  directionHi := (314414430760370296953/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree113.table
  base := (2176754043468940952319791303511987110411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-33658829099543727878252053150200000000000000)
      constant := (1301387797906538632631920987942370516433189180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree113.table
  base := (5441885108661737556856791102389595961349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-152891447723563221959414138876580000000000000)
      constant := (5966476655290515130701908440670708301828847316) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39301803845046287119/12500000000000000000)
  centralHi := (314414430760370296953/100000000000000000000)
  directionLo := (493460855321553401/156250000000000000)
  directionHi := (315814947405794176641/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree114.table
  base := (11385668624458443262748707489454849871/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-33953431383594321552321648958600000000000000)
      constant := (1324481207353880517263218215501371478512796000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree114.table
  base := (11385668624441370518763772831302459135437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-51409927937988163454824386611580000000000000)
      constant := (2024115299977999873168634875296000693563333118) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493460855321553401/156250000000000000)
  centralHi := (315814947405794176641/100000000000000000000)
  directionLo := (158604640332085962187/50000000000000000000)
  directionHi := (507534849062675079/160000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree115.table
  base := (11894379927087636768838069968610640691773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-34248033667644915226391244767000000000000000)
      constant := (1347777512317471056758478386848780793107638548) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree115.table
  base := (5947189963536954000570393924957821637143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-155568119904365758769532180792900000000000000)
      constant := (6179145251620912306245899884121193386840378012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158604640332085962187/50000000000000000000)
  centralHi := (507534849062675079/160000000000000000)
  directionLo := (159298755859892272613/50000000000000000000)
  directionHi := (318597511719784545227/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree116.table
  base := (12409904093842704189023875600683666348529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-34542635951695508900460840575400000000000000)
      constant := (1371276712776090894300291520177062158451605604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree116.table
  base := (12409904093831665233615799974711537466163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-156906455994767027174591201751060000000000000)
      constant := (6286874710255766568202464122766552496972067846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159298755859892272613/50000000000000000000)
  centralHi := (318597511719784545227/100000000000000000000)
  directionLo := (3999746499947588573/1250000000000000000)
  directionHi := (319979719995807085841/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree117.table
  base := (51728964375882587419973069367943341287/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 520000000000000000000000000000000000000000
      center := (595)
      previous := (0)
      next := (289)
      square := (16834416231462495661119760480000000000000)
      linear := (-2679787556595854044194648952600000000000000)
      constant := (107306062208380846368375240317283263436731000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree117.table
  base := (12932241093961771349655762260644719076377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 780000000000000000000000000000000000000000
      center := (901)
      previous := (0)
      next := (425)
      square := (25251624347193743491679640720000000000000)
      linear := (-4057558771414571681529492889980000000000000)
      constant := (163988058352436209543579584949160288087957406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3999746499947588573/1250000000000000000)
  centralHi := (319979719995807085841/100000000000000000000)
  directionLo := (80338995801833355127/25000000000000000000)
  directionHi := (321355983207333420509/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree118.table
  base := (13461390897337212211883256427020662129557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-35131840519796696248600032192200000000000000)
      constant := (1418883800095680627497150818286165967599580532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree118.table
  base := (13461390897330076663202605719381297592241/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-159583128175569563984709243667380000000000000)
      constant := (6505123947996981034892330309010777907275597122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80338995801833355127/25000000000000000000)
  centralHi := (321355983207333420509/100000000000000000000)
  directionLo := (80681594353091466761/25000000000000000000)
  directionHi := (64545275482473173409/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree119.table
  base := (13997353474409694302309800665676745614211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-35426442803847289922669628000600000000000000)
      constant := (1442991686916315659197917990140997480035206636) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree119.table
  base := (13997353474403958009557159234016573817367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-160921464265970832389768264625540000000000000)
      constant := (6615643726921834916613628732209508417552430414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80681594353091466761/25000000000000000000)
  centralHi := (64545275482473173409/20000000000000000000)
  directionLo := (64818195412172859431/20000000000000000000)
  directionHi := (81022744265216074289/25000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree120.table
  base := (2908025759248068593327979188613355208021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-35721045087897883596739223809000000000000000)
      constant := (1467302469151287418783267728907513140603110980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree120.table
  base := (14540128796235731857937292112981298382741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-54086600118790700264942428527900000000000000)
      constant := (2242364537477171654687619947016563036560099374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64818195412172859431/20000000000000000000)
  centralHi := (81022744265216074289/25000000000000000000)
  directionLo := (16272492752097212289/5000000000000000000)
  directionHi := (325449855041944245781/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree121.table
  base := (603588673378014210228822168550995198173/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-36015647371948477270808819617400000000000000)
      constant := (1491816146781411835459572614667011818849123700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree121.table
  base := (15089716834446648875307522177234932580603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-163598136446773369199886306541860000000000000)
      constant := (6839473604439693021768929698742678664910194326) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16272492752097212289/5000000000000000000)
  centralHi := (325449855041944245781/100000000000000000000)
  directionLo := (163401541364654342701/50000000000000000000)
  directionHi := (326803082729308685403/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree122.table
  base := (3911529390303606000380049701001471138903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-36310249655999070944878415425800000000000000)
      constant := (1516532719787879001581243301588007977959593712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree122.table
  base := (15646117561211445034781905550286964609987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-164936472537174637604945327500020000000000000)
      constant := (6952783702861724636562051264016192946343580454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163401541364654342701/50000000000000000000)
  centralHi := (326803082729308685403/100000000000000000000)
  directionLo := (82037682506248398077/25000000000000000000)
  directionHi := (328150730024993592309/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree123.table
  base := (1620933094924581983126799094639012340433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-36604851940049664618948011234200000000000000)
      constant := (1541452188152243088092286702663759723421327080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree123.table
  base := (31658849510241065768296669688970902429/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-55424936209191968670001449486060000000000000)
      constant := (2355674635871534561092467069275773645472259072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82037682506248398077/25000000000000000000)
  centralHi := (328150730024993592309/100000000000000000000)
  directionLo := (82373216350375792779/25000000000000000000)
  directionHi := (329492865401503171117/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree124.table
  base := (4194839242945496038465106708435026316799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-36899454224100258293017607042600000000000000)
      constant := (1566574551856412605385116849320608311160624496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree124.table
  base := (524354905368126878871408800543221950423/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-167613144717977174415063369416340000000000000)
      constant := (7182194218616918543625416727363159397541976512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82373216350375792779/25000000000000000000)
  centralHi := (329492865401503171117/100000000000000000000)
  directionLo := (330829555942406602611/100000000000000000000)
  directionHi := (82707388985601650653/25000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree125.table
  base := (4339048900642652951004128260253879273903/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-37194056508150851967087202851000000000000000)
      constant := (1591899810882640995168003790003226489556633712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree125.table
  base := (17356195602569065683962600479590045525111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-168951480808378442820122390374500000000000000)
      constant := (7298294635788809773625485650440162918487387662) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (330829555942406602611/100000000000000000000)
  centralHi := (82707388985601650653/25000000000000000000)
  directionLo := (166080433690732210063/50000000000000000000)
  directionHi := (332160867381464420127/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree126.table
  base := (3587969363171240621729097520385807076317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-37488658792201445641156798659400000000000000)
      constant := (1617427965213517539661938169622404027917951460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree126.table
  base := (17939846815854960748970350638811353462813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-56763272299593237075060470444220000000000000)
      constant := (2471775053017309732745441070112614712411292382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (166080433690732210063/50000000000000000000)
  centralHi := (332160867381464420127/100000000000000000000)
  directionLo := (33348686414034908511/10000000000000000000)
  directionHi := (333486864140349085111/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree127.table
  base := (9265155293183533074375029476940800052161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-37783261076252039315226394467800000000000000)
      constant := (1643159014831958575129677819081823961670521672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree127.table
  base := (9265155293183033966239878167203853826629/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-171628152989180979630240432290820000000000000)
      constant := (7533285788329400374848413679592338246681210836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33348686414034908511/10000000000000000000)
  centralHi := (333486864140349085111/100000000000000000000)
  directionLo := (167403804682510503933/50000000000000000000)
  directionHi := (334807609365021007867/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree128.table
  base := (19127586889302750935362852709688127973189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-38077863360302632989295990276200000000000000)
      constant := (1669092959721198997378680793295749174509875764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree128.table
  base := (19127586889301948933255570440268429679681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30420000000000000000000000000000000000000000
      center := (35139)
      previous := (0)
      next := (16575)
      square := (984813349540555996175505988080000000000000)
      linear := (-172966489079582248035299453248980000000000000)
      constant := (7652176523545780370149399436446016563085589602) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell185.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167403804682510503933/50000000000000000000)
  centralHi := (334807609365021007867/100000000000000000000)
  directionLo := (336123164960818130821/100000000000000000000)
  directionHi := (168061582480409065411/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 35
  qDenominator := 52
  table := BinomialMassData.Q35_52.Degree129.table
  base := (2466459462540237263148644933339148366103/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6760000000000000000000000000000000000000000
      center := (7735)
      previous := (0)
      next := (3757)
      square := (218847411009012443594556886240000000000000)
      linear := (-38372465644353226663365586084600000000000000)
      constant := (1695229799864784047479359868707998114363885024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q35_52.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 78
  table := BinomialMassData.Q53_78.Degree129.table
  base := (1973167570032125378708156485234381790221/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10140000000000000000000000000000000000000000
      center := (11713)
      previous := (0)
      next := (5525)
      square := (328271116513518665391835329360000000000000)
      linear := (-58101608389994505480119491402380000000000000)
      constant := (2590665788209007599182711571668786631352840940) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_78.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell185.Kernel129
