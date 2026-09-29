import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell016.Parameters
import ForestUnimodality.BinomialMassData.Q19_51.Batch000_049
import ForestUnimodality.BinomialMassData.Q19_51.Batch050_099
import ForestUnimodality.BinomialMassData.Q97_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q97_255.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree000.table
  base := (126454248882332474665401989/12500000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (288)
      previous := (171)
      next := (0)
      square := (7494356253906618511861914610000000000000)
      linear := (18729558946370266220293743100000000000000)
      constant := (1719777784799721655449467050400000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree000.table
  base := (126454248882332474665401989/12500000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1422)
      previous := (873)
      next := (0)
      square := (37471781269533092559309573050000000000000)
      linear := (93647794731851331101468715500000000000000)
      constant := (8598888923998608277247335252000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree001.table
  base := (33466905604414672541625280196072568242983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (2011265905849296221352684428760000000000000)
      constant := (173186402953496156050671031939399499999997566) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree001.table
  base := (66220467959464726881442569831752979623221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (9966397254199601684621079168480000000000000)
      constant := (856576465312303935900444656179441499999989105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (12087086280331326373/25000000000000000000)
  directionHi := (48348345121325305493/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree002.table
  base := (22186436867276574081822401817211610918877/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (1156909292903941711000426163220000000000000)
      constant := (113915254300783066679298918404254799999998154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree002.table
  base := (8688531660564438731786989852949142637447/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (5604681914425949710717444865460000000000000)
      constant := (557389492532850774703796115742193999999991175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12087086280331326373/25000000000000000000)
  centralHi := (48348345121325305493/100000000000000000000)
  directionLo := (68374885388873310623/100000000000000000000)
  directionHi := (2136715168402290957/3125000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree003.table
  base := (29407108760619725415925798705255057137491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (33616964439843022294240877520000000000000)
      constant := (8301937671112200250710042423048711512734899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree003.table
  base := (14246237445808520523063275138783538466899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (138107397183588637423756729160000000000000)
      constant := (40184440153447618765673886829978426169338110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68374885388873310623/100000000000000000000)
  centralHi := (2136715168402290957/3125000000000000000)
  directionLo := (41870895106005142003/50000000000000000000)
  directionHi := (83741790212010284007/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree004.table
  base := (151460635885156710721216371190797181917/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-551803932986767309704090367860000000000000)
      constant := (48701464892587187307855234059089724181262976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree004.table
  base := (18581903077972048246175558340414129417971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-3118748765121354237089823740580000000000000)
      constant := (233129741361194061999323455402189753080712855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41870895106005142003/50000000000000000000)
  centralHi := (83741790212010284007/100000000000000000000)
  directionLo := (12087086280331326373/12500000000000000000)
  directionHi := (19339338048530122197/20000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree005.table
  base := (1573277233461932078704459848527050986107/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-1406160545932121820056348633400000000000000)
      constant := (31377449856013723413225376647900876918914456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree005.table
  base := (11915738839897941909919612729676645094111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-7480464104895006210993458043600000000000000)
      constant := (148452204167376754122715036328794769448913555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12087086280331326373/12500000000000000000)
  centralHi := (19339338048530122197/20000000000000000000)
  directionLo := (5405509314545185007/5000000000000000000)
  directionHi := (108110186290903700141/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree006.table
  base := (3947496160471726485089533910655014034851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-251168573208608481156511877660000000000000)
      constant := (2206508977887126446782859227078598112143878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree006.table
  base := (3676277958855669577123097624852137713333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-1315797716074295353877454705180000000000000)
      constant := (10309233476932694540706825012798677991532370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5405509314545185007/5000000000000000000)
  centralHi := (108110186290903700141/100000000000000000000)
  directionLo := (118428775455227446231/100000000000000000000)
  directionHi := (14803596931903430779/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree007.table
  base := (2296425233954368717915854987110600604279/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-3114873771822830840760865164480000000000000)
      constant := (12271008151861488369661392236419344343459358) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree007.table
  base := (4159834685793413336709097923535102395523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-16203894784442310158800726649640000000000000)
      constant := (56596015005073711745249687020980006653776615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118428775455227446231/100000000000000000000)
  centralHi := (14803596931903430779/12500000000000000000)
  directionLo := (15989712186568716153/12500000000000000000)
  directionHi := (5116707899701989169/4000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree008.table
  base := (2211690189553163234403518280005630637179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-3969230384768185351113123430020000000000000)
      constant := (7397198297027554652585938025014645287302579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree008.table
  base := (1866935161379975641242440143304854989313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-20565610124215962132704360952660000000000000)
      constant := (33770272329566861206443044740895639136015565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15989712186568716153/12500000000000000000)
  centralHi := (5116707899701989169/4000000000000000000)
  directionLo := (68374885388873310623/50000000000000000000)
  directionHi := (136749770777746621247/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree009.table
  base := (89361832753587370003391452920665965167/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-535954110857059984607264632840000000000000)
      constant := (493846721853040548335766737940362319666315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree009.table
  base := (170860202492139591647157254333526078009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-2769702829332179345178666139520000000000000)
      constant := (2262821714937586736330295826757945182723005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68374885388873310623/50000000000000000000)
  centralHi := (136749770777746621247/100000000000000000000)
  directionLo := (36261258840993979119/25000000000000000000)
  directionHi := (145045035363975916477/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree010.table
  base := (-450323848051977080425783450506934117717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-5677943610658894371817639961100000000000000)
      constant := (2896052670416029851364412536462928719636166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree010.table
  base := (-562012247864029860996890696476158571957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-29289040803763266080511629558700000000000000)
      constant := (13837160185010136353367556523055115543398430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36261258840993979119/25000000000000000000)
  centralHi := (145045035363975916477/100000000000000000000)
  directionLo := (30578178336655573041/20000000000000000000)
  directionHi := (76445445841638932603/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree011.table
  base := (-1960918441855429426504125565600457792593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-6532300223604248882169898226640000000000000)
      constant := (2412745645530165448399786131903209281465607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree011.table
  base := (-107226827061144951276411465975377040333/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-33650756143536918054415263861720000000000000)
      constant := (12536303589993119565976391947578431809386700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30578178336655573041/20000000000000000000)
  centralHi := (76445445841638932603/50000000000000000000)
  directionLo := (16035332000204606041/10000000000000000000)
  directionHi := (160353320002046060411/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree012.table
  base := (-35246365071832413820826011964649214287/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-820739648505511488058017388020000000000000)
      constant := (307975308001248978809261585857310165684560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree012.table
  base := (-297332772189963450039409366618438126137/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-4223607942590063336479877573860000000000000)
      constant := (1709771016405929291688798483067569077320350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16035332000204606041/10000000000000000000)
  centralHi := (160353320002046060411/100000000000000000000)
  directionLo := (41870895106005142003/25000000000000000000)
  directionHi := (167483580424020568013/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree013.table
  base := (-441722455709793026332172150828368153087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-8241013449494957902874414757720000000000000)
      constant := (3825517179659017602970942274433315470565704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree013.table
  base := (-3664653769426710186396192183132561326597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-42374186823084222002222532467760000000000000)
      constant := (21686471067642753793374284882447039947606015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41870895106005142003/25000000000000000000)
  centralHi := (167483580424020568013/100000000000000000000)
  directionLo := (174322437418767599383/100000000000000000000)
  directionHi := (21790304677345949923/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree014.table
  base := (-2070516424552265035361997013688903292323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-9095370062440312413226673023260000000000000)
      constant := (5475377938006038926093756902470325073335754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree014.table
  base := (-2127234000374551533831785134873039305479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-46735902162857873976126166770780000000000000)
      constant := (30964326463091864391903452132976247664491210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174322437418767599383/100000000000000000000)
  centralHi := (21790304677345949923/12500000000000000000)
  directionLo := (180902942661502680617/100000000000000000000)
  directionHi := (90451471330751340309/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree015.table
  base := (-933410364719122471716828183746811682849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-1105525186153962991508770143200000000000000)
      constant := (850535404929059329767970583235857118283195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree015.table
  base := (-4766886881384998984190074275772180136733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-5677513055847947327781089008200000000000000)
      constant := (4767541188881854285740746257859199702420815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180902942661502680617/100000000000000000000)
  centralHi := (90451471330751340309/50000000000000000000)
  directionLo := (1462908870871730631/781250000000000000)
  directionHi := (187252335471581520769/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree016.table
  base := (-5129337985708305791909370018593368963449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-10804083288331021433931189554340000000000000)
      constant := (10318318114261487747761170203718647326069151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree016.table
  base := (-2609168062394345021643283838906122140893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-55459332842405177923933435376820000000000000)
      constant := (57303487374704157477086297932515763115373070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1462908870871730631/781250000000000000)
  centralHi := (187252335471581520769/100000000000000000000)
  directionLo := (12087086280331326373/6250000000000000000)
  directionHi := (193393380485301221969/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree017.table
  base := (-43281743258941916325779603293856091557/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2592)
      previous := (1539)
      next := (0)
      square := (67449206285159566606757231490000000000000)
      linear := (-685790582428022114369614577640000000000000)
      constant := (790248087734065618901340066603122302947712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree017.table
  base := (-2810106735957022697466520729350030300963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (12798)
      previous := (7857)
      next := (0)
      square := (337246031425797833033786157450000000000000)
      linear := (-3518885187186989993990415863520000000000000)
      constant := (4353114639193482518392494955092453639526610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12087086280331326373/6250000000000000000)
  centralHi := (193393380485301221969/100000000000000000000)
  directionLo := (4983633343976013499/2500000000000000000)
  directionHi := (199345333759040539961/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree018.table
  base := (-5907859485072857259715125749902272152921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-1390310723802414494959522898380000000000000)
      constant := (1886673822796581795779279725558243347805831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree018.table
  base := (-186893826148377196721367192691940991503/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-7131418169105831319082300442540000000000000)
      constant := (10322347675032313469415553871108648552901280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4983633343976013499/2500000000000000000)
  centralHi := (199345333759040539961/100000000000000000000)
  directionLo := (205124656166619931869/100000000000000000000)
  directionHi := (20512465616661993187/10000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree019.table
  base := (-3119493407618753365338934610907049064513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-13367153127167084964987964350960000000000000)
      constant := (20939577152610860270126183899691530766403374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree019.table
  base := (-788172307185094678007316072694430915129/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-68544478861726133845644338285880000000000000)
      constant := (113921617928048157905729558410405407589978840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205124656166619931869/100000000000000000000)
  centralHi := (20512465616661993187/10000000000000000000)
  directionLo := (21074555047128475237/10000000000000000000)
  directionHi := (210745550471284752371/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree020.table
  base := (-6538096071665391686579107403160514832623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-14221509740112439475340222616500000000000000)
      constant := (25300658628390078209299960962379500920347577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree020.table
  base := (-6598925692023386603565521032953101421319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-72906194201499785819547972588900000000000000)
      constant := (137007399450925018774326717962044916015746405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21074555047128475237/10000000000000000000)
  centralHi := (210745550471284752371/100000000000000000000)
  directionLo := (216220372581807400281/100000000000000000000)
  directionHi := (108110186290903700141/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree021.table
  base := (-1702182783604424646480464691440004457171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-1675096261450865998410275653560000000000000)
      constant := (3339343466718638222329833074765354847510324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree021.table
  base := (-2681485932501507675530166174309413333/3906250000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-8585323282363715310383511876880000000000000)
      constant := (18012753203991615635185580943200618198566400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216220372581807400281/100000000000000000000)
  centralHi := (108110186290903700141/50000000000000000000)
  directionLo := (110779975622161054267/50000000000000000000)
  directionHi := (44311990248864421707/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree022.table
  base := (-1763415130247471591104122134155048223091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-15930222966003148496044739147580000000000000)
      constant := (35192673954838168953349134075770878286961236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree022.table
  base := (-7105055263173899213876365755316297444343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-81629624881047089767355241194940000000000000)
      constant := (189209397911473570637742463669407551736319285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110779975622161054267/50000000000000000000)
  centralHi := (44311990248864421707/20000000000000000000)
  directionLo := (226773839918446436133/100000000000000000000)
  directionHi := (113386919959223218067/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree023.table
  base := (-3637549187934188490897935629645003531677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-16784579578948503006396997413120000000000000)
      constant := (40710647901692169549176663483256691628216246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree023.table
  base := (-1830601605600836473354814421325132788351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-85991340220820741741258875497960000000000000)
      constant := (218263596310951831582709839059592592349980980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226773839918446436133/100000000000000000000)
  centralHi := (113386919959223218067/50000000000000000000)
  directionLo := (11593525881642731597/5000000000000000000)
  directionHi := (231870517632854631941/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree024.table
  base := (-3737426596532901250473840773783782047221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-1959881799099317501861028408740000000000000)
      constant := (5178145460900321088097804913872973976706262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree024.table
  base := (-1879601339562637632909837013727213570087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-10039228395621599301684723311220000000000000)
      constant := (27694960297914885647762142029072705564897140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11593525881642731597/5000000000000000000)
  centralHi := (231870517632854631941/100000000000000000000)
  directionLo := (118428775455227446231/50000000000000000000)
  directionHi := (236857550910454892463/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree025.table
  base := (-765442919064534920287165897171622466731/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-18493292804839212027101513944200000000000000)
      constant := (52866745222887982167579553678316099640326690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree025.table
  base := (-7694513512486688341311851408981329405941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-94714770900368045689066144104000000000000000)
      constant := (282163530972085854737049116119947811075737295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118428775455227446231/50000000000000000000)
  centralHi := (236857550910454892463/100000000000000000000)
  directionLo := (12087086280331326373/5000000000000000000)
  directionHi := (241741725606626527461/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree026.table
  base := (-7815096508772088606786868189774607039621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-19347649417784566537453772209740000000000000)
      constant := (59497652491478095651785804668076247089945779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree026.table
  base := (-3925985019274839895111062269894361455791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-99076486240141697662969778407020000000000000)
      constant := (316974145993047327620730787550991658534876090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12087086280331326373/5000000000000000000)
  centralHi := (241741725606626527461/100000000000000000000)
  directionLo := (24652915522355625067/10000000000000000000)
  directionHi := (246529155223556250671/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree027.table
  base := (-3978970371778761293285727390308577144309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-2244667336747769005311781163920000000000000)
      constant := (7388134146487468207949104504831642410589398) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree027.table
  base := (-7991837258558995360800301256370743602897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-11493133508879483292985934745560000000000000)
      constant := (39296963582772741761877822485358275493813835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24652915522355625067/10000000000000000000)
  centralHi := (246529155223556250671/100000000000000000000)
  directionLo := (251225370636030852019/100000000000000000000)
  directionHi := (12561268531801542601/5000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree028.table
  base := (-8083898665751709643337820537538791371769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-21056362643675275558158288740820000000000000)
      constant := (73850973162894434665454604240181603642028831) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree028.table
  base := (-8115033665513412022004698409256351473153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-107799916919689001610777047013060000000000000)
      constant := (392247164726358804964255049930517149091645235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251225370636030852019/100000000000000000000)
  centralHi := (12561268531801542601/5000000000000000000)
  directionLo := (255835394985099458449/100000000000000000000)
  directionHi := (5116707899701989169/2000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree029.table
  base := (-256055768764333579688324081015330938873/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-21910719256620630068510547006360000000000000)
      constant := (81568831965404189599105802009961975295722464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree029.table
  base := (-4111179260135782447249923067694472485623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-112161632259462653584680681316080000000000000)
      constant := (432687229049793165198552515806920770648945770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255835394985099458449/100000000000000000000)
  centralHi := (5116707899701989169/2000000000000000000)
  directionLo := (130181903315277113829/50000000000000000000)
  directionHi := (260363806630554227659/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree030.table
  base := (-8288310405466062523979309337095387560833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-2529452874396220508762533919100000000000000)
      constant := (9960548020423423718020940025579432994919263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree030.table
  base := (-4157255340213852987584932017573992685749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-12947038622137367284287146179900000000000000)
      constant := (52775975174693834371146091621611161138185390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130181903315277113829/50000000000000000000)
  centralHi := (260363806630554227659/100000000000000000000)
  directionLo := (264814792409947171499/100000000000000000000)
  directionHi := (529629584819894343/200000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree031.table
  base := (-4184050493392817067877387196844932404393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-23619432482511339089215063537440000000000000)
      constant := (98077648437577717010680862945242661632347614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree031.table
  base := (-2098025847619945360781462335346942438279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-120885062939009957532487949922120000000000000)
      constant := (519128832049017047330202156779986054360726420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264814792409947171499/100000000000000000000)
  centralHi := (529629584819894343/200000000000000000)
  directionLo := (67298048242080447119/25000000000000000000)
  directionHi := (269192192968321788477/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree032.table
  base := (-421685332006977762586710625779273846199/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-24473789095456693599567321802980000000000000)
      constant := (106865549407531546826124867149682174520728020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree032.table
  base := (-8455676177942912251060156697216087827381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-125246778278783609506391584225140000000000000)
      constant := (565115378924776631178450440229760777804910095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67298048242080447119/25000000000000000000)
  centralHi := (269192192968321788477/100000000000000000000)
  directionLo := (273499541555493242493/100000000000000000000)
  directionHi := (136749770777746621247/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree033.table
  base := (-8485613083298375981900999697334800507607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-2814238412044672012213286674280000000000000)
      constant := (12889707971305678008050412431300242653301577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree033.table
  base := (-1063213077765391756577625656523247073381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-14400943735395251275588357614240000000000000)
      constant := (68104136921183140801040509433765263831715640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273499541555493242493/100000000000000000000)
  centralHi := (136749770777746621247/50000000000000000000)
  directionLo := (69435024351473620819/25000000000000000000)
  directionHi := (277740097405894483277/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree034.table
  base := (-8524249766802827030865080723637720433723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2592)
      previous := (1539)
      next := (0)
      square := (67449206285159566606757231490000000000000)
      linear := (-1540147195373376624721872843180000000000000)
      constant := (7382470496434114246292760632723428773640381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree034.table
  base := (-8542608516891452983116073230864476637341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (12798)
      previous := (7857)
      next := (0)
      square := (337246031425797833033786157450000000000000)
      linear := (-7880600526960641967894050166540000000000000)
      constant := (38975819572196442390192249146580675372434135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69435024351473620819/25000000000000000000)
  centralHi := (277740097405894483277/100000000000000000000)
  directionLo := (140958437298913164373/50000000000000000000)
  directionHi := (281916874597826328747/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree035.table
  base := (-8549996868228730821692318881526755336349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-27036858934292757130624096599600000000000000)
      constant := (135348440658543353047300213363898909370156251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree035.table
  base := (-8566758788523107984220586123625871185231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-138331924298104565428102487134200000000000000)
      constant := (714065656338640909013675084491395545236070845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140958437298913164373/50000000000000000000)
  centralHi := (281916874597826328747/100000000000000000000)
  directionLo := (143016333559297796397/50000000000000000000)
  directionHi := (57206533423719118559/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree036.table
  base := (-535199453406314343573191796208046058867/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-3099023949693123515664039429460000000000000)
      constant := (16171758023152173348892338830253995023798992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree036.table
  base := (-1715696684826757243917894654604810042699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-15854848848653135266889569048580000000000000)
      constant := (85262570850234768976361419533616247441499725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143016333559297796397/50000000000000000000)
  centralHi := (57206533423719118559/20000000000000000000)
  directionLo := (36261258840993979119/12500000000000000000)
  directionHi := (290090070727951832953/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree037.table
  base := (-8564131616292068465388979485745524228477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-28745572160183466151328613130680000000000000)
      constant := (156093366194419793058733463541645891481731323) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree037.table
  base := (-1715614519204902470925742038644359191083/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-147055354977651869375909755740240000000000000)
      constant := (822477602976980730180396597863636543599827925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36261258840993979119/12500000000000000000)
  centralHi := (290090070727951832953/100000000000000000000)
  directionLo := (147045751052962150317/50000000000000000000)
  directionHi := (58818300421184860127/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree038.table
  base := (-8553082924304466317542212722260904617999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-29599928773128820661680871396220000000000000)
      constant := (166990383427896540847706239246519387088584601) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree038.table
  base := (-4282891559947206802134374586641482914301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-151417070317425521349813390043260000000000000)
      constant := (879405712425077187762936018655391029399030990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147045751052962150317/50000000000000000000)
  centralHi := (58818300421184860127/20000000000000000000)
  directionLo := (298039215686274509803/100000000000000000000)
  directionHi := (74509803921568627451/25000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree039.table
  base := (-533142520012552111352734397258752078219/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-3383809487341575019114792184640000000000000)
      constant := (19804029145037261444820845627345530390315344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree039.table
  base := (-8541842352413307329342721269934694615887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-17308753961911019258190780482920000000000000)
      constant := (104238278802545702084137352087230366280043285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298039215686274509803/100000000000000000000)
  centralHi := (74509803921568627451/25000000000000000000)
  directionLo := (301935318508551493857/100000000000000000000)
  directionHi := (150967659254275746929/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree040.table
  base := (-4247966264617505047829363004254645228901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-31308641999019529682385387927300000000000000)
      constant := (189830459932350993667830265191867335519256998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree040.table
  base := (-8506451610935638610301286283107963295781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-160140500996972825297620658649300000000000000)
      constant := (998691375238288564892036217554580937338368095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301935318508551493857/100000000000000000000)
  centralHi := (150967659254275746929/50000000000000000000)
  directionLo := (30578178336655573041/10000000000000000000)
  directionHi := (305781783366555730411/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree041.table
  base := (-4225112431724337875104600908529027774069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-32162998611964884192737646192840000000000000)
      constant := (201772494312323051884926219263661997519293062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree041.table
  base := (-8459789181880935573257499922787839376073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-164502216336746477271524292952320000000000000)
      constant := (1061043991856322962887235875455558148914170635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30578178336655573041/10000000000000000000)
  centralHi := (305781783366555730411/100000000000000000000)
  directionLo := (309580460486126286837/100000000000000000000)
  directionHi := (154790230243063143419/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree042.table
  base := (-2098330467784492765467757208595381427541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-3668595024990026522565544939820000000000000)
      constant := (23784659717237029632362409363743739069762604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree042.table
  base := (-4201006486184828284054639869661505408823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-18762659075168903249491991917260000000000000)
      constant := (125022256166101439100268080527302249368501530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309580460486126286837/100000000000000000000)
  centralHi := (154790230243063143419/50000000000000000000)
  directionLo := (4895829498881906597/1562500000000000000)
  directionHi := (313333087928442022209/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree043.table
  base := (-2081342419635593559615111968234932422929/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-33871711837855593213442162723920000000000000)
      constant := (226698409286432755268306617868753763071846684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree043.table
  base := (-8333262850702118463991106461845501900379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-173225647016293781219331561558360000000000000)
      constant := (1191158497166812911054472843542705247785571105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4895829498881906597/1562500000000000000)
  centralHi := (313333087928442022209/100000000000000000000)
  directionLo := (9907540652650851373/3125000000000000000)
  directionHi := (317041300884827243937/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree044.table
  base := (-8246498062295769768745527405948639723771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-34726068450800947723794420989460000000000000)
      constant := (239681572257196784060775273950007588078471629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree044.table
  base := (-4126831357148947963231304826309039534621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-177587362356067433193235195861380000000000000)
      constant := (1258916955586081271817813249389285881704507790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9907540652650851373/3125000000000000000)
  centralHi := (317041300884827243937/100000000000000000000)
  directionLo := (320706640004092120821/100000000000000000000)
  directionHi := (160353320002046060411/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree045.table
  base := (-8156822285402839818083481995713813480847/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-3953380562638478026016297695000000000000000)
      constant := (28112347396483352750730393048988707904035217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree045.table
  base := (-8163322318178603010574773338621402726021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-20216564188426787240793203351600000000000000)
      constant := (147608250376517993711832877223842073060899655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320706640004092120821/100000000000000000000)
  centralHi := (160353320002046060411/50000000000000000000)
  directionLo := (162165279436355550211/50000000000000000000)
  directionHi := (324330558872711100423/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree046.table
  base := (-8056444724893802885199838266332846262057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-36434781676691656744498937520540000000000000)
      constant := (266686805937237329040516313592148266872389743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree046.table
  base := (-1007792361572827234026616685972888684061/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-186310793035614737141042464467420000000000000)
      constant := (1399829126095304817903231986155684661310293560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162165279436355550211/50000000000000000000)
  centralHi := (324330558872711100423/100000000000000000000)
  directionLo := (81978607687713224839/25000000000000000000)
  directionHi := (327914430750852899357/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree047.table
  base := (-1589091263110404454851720713328811865027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-37289138289637011254851195786080000000000000)
      constant := (280708373842486718958473019289428801695323865) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree047.table
  base := (-7950798574579455769023275415308466802307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-190672508375388389114946098770440000000000000)
      constant := (1472980453493420849382332882788359389235997465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81978607687713224839/25000000000000000000)
  centralHi := (327914430750852899357/100000000000000000000)
  directionLo := (66291910930558241691/20000000000000000000)
  directionHi := (41432444331598901057/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree048.table
  base := (-7823937830987690686810334916803848412201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-4238166100286929529467050450180000000000000)
      constant := (32786180021326470365967850635923687808873911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree048.table
  base := (-391438883771073795121978503400252861717/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-21670469301684671232094414785940000000000000)
      constant := (171991915906130345158794710416596692296378700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66291910930558241691/20000000000000000000)
  centralHi := (41432444331598901057/12500000000000000000)
  directionLo := (13398686433921645441/4000000000000000000)
  directionHi := (167483580424020568013/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree049.table
  base := (-1538392204139693792346831274976717120363/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-38997851515527720275555712317160000000000000)
      constant := (309788358365148456204304621218757793849679185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree049.table
  base := (-3848171901351890146603635255602409587351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-199395939054935693062753367376480000000000000)
      constant := (1624668615843787287263895901924075326633000490) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13398686433921645441/4000000000000000000)
  centralHi := (167483580424020568013/50000000000000000000)
  directionLo := (67687683169855427689/20000000000000000000)
  directionHi := (169219207924638569223/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree050.table
  base := (-943698702438783507847425361777233401677/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-39852208128473074785907970582700000000000000)
      constant := (324846422587835193273542895562139327377904984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree050.table
  base := (-377677842705412731008527801318385205839/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-203757654394709345036657001679500000000000000)
      constant := (1703203792589910468633194855757088007961276100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67687683169855427689/20000000000000000000)
  centralHi := (169219207924638569223/50000000000000000000)
  directionLo := (85468606736091638279/25000000000000000000)
  directionHi := (341874426944366553117/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree051.table
  base := (-7396880243853244489910458995119936274269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (288)
      previous := (171)
      next := (0)
      square := (7494356253906618511861914610000000000000)
      linear := (-266055978702081237230459012080000000000000)
      constant := (2223854023533749068268092252392961083337427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree051.table
  base := (-1850117474379441659647663009090119673397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 850000000000000000000000000000000000000000
      center := (1422)
      previous := (873)
      next := (0)
      square := (37471781269533092559309573050000000000000)
      linear := (-1360257318526032660199742718840000000000000)
      constant := (11657072439514548727973052409307359311045020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85468606736091638279/25000000000000000000)
  centralHi := (341874426944366553117/100000000000000000000)
  directionLo := (345276246322433544729/100000000000000000000)
  directionHi := (34527624632243354473/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree052.table
  base := (-7233883187644224726017492895802266875201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-41560921354363783806612487113780000000000000)
      constant := (355997956589156033036732950845138303857602199) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree052.table
  base := (-3618564975275573887294704444925991608317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-212481085074256648984464270285540000000000000)
      constant := (1865652876347100844807227726740450958267674830) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345276246322433544729/100000000000000000000)
  centralHi := (34527624632243354473/10000000000000000000)
  directionLo := (174322437418767599383/50000000000000000000)
  directionHi := (348644874837535198767/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree053.table
  base := (-7060643129075402204106924717035491355609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-42415277967309138316964745379320000000000000)
      constant := (372091179345334574929437705515060686984060991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree053.table
  base := (-7063578671049725247780372697318071392437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-216842800414030300958367904588560000000000000)
      constant := (1949565630133808676424172812939624481541356815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174322437418767599383/50000000000000000000)
  centralHi := (348644874837535198767/100000000000000000000)
  directionLo := (351981265448107855483/100000000000000000000)
  directionHi := (87995316362026963871/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree054.table
  base := (-1375439951663577651577816093641008862961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-4807737175583832536368555960540000000000000)
      constant := (43169914515007130282683535630608742193021355) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree054.table
  base := (-687985296871089684905722224800002029467/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-24578279528200439214696837654620000000000000)
      constant := (226141096066137199106682220507495970674201850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (351981265448107855483/100000000000000000000)
  centralHi := (87995316362026963871/25000000000000000000)
  directionLo := (355286326365682338693/100000000000000000000)
  directionHi := (177643163182841169347/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree055.table
  base := (-417724270938240741778957706879034403647/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-44123991193199847337669261910400000000000000)
      constant := (405312018748020746361035852745272104257826448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree055.table
  base := (-3342992773444217438524130561598411852429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-225566231093577604906175173194600000000000000)
      constant := (2122765154424263382671468153549175307718321710) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355286326365682338693/100000000000000000000)
  centralHi := (177643163182841169347/50000000000000000000)
  directionLo := (71712184788470341457/20000000000000000000)
  directionHi := (179280461971175853643/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree056.table
  base := (-6479840183411703498724268240861410320597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-44978347806145201848021520175940000000000000)
      constant := (422439462209818574766100908113999471756127203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree056.table
  base := (-6482005382542091154778760639354877948661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-229927946433351256880078807497620000000000000)
      constant := (2212051122775532876099713666414373812277663695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71712184788470341457/20000000000000000000)
  centralHi := (179280461971175853643/50000000000000000000)
  directionLo := (180902942661502680617/50000000000000000000)
  directionHi := (72361177064601072247/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree057.table
  base := (-12238248305015277753376577689402325469/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-5092522713232284039819308715720000000000000)
      constant := (48879054293126446869059778816284516705003008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree057.table
  base := (-250717526056127230639108599531306439139/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-26032184641458323205998049088960000000000000)
      constant := (255903048415128613286775661522065554886103625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180902942661502680617/50000000000000000000)
  centralHi := (72361177064601072247/20000000000000000000)
  directionLo := (73004400177067268809/20000000000000000000)
  directionHi := (182511000442668172023/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree058.table
  base := (-6042041904941198511349946698259804848981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-46687061032035910868726036707020000000000000)
      constant := (457728033726736851211167471010546247587800419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree058.table
  base := (-3021903302306634110240510965418409317339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-238651377112898560827886076103660000000000000)
      constant := (2395993797427541266664854165021883173656012610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73004400177067268809/20000000000000000000)
  centralHi := (182511000442668172023/50000000000000000000)
  directionLo := (368210026488015759471/100000000000000000000)
  directionHi := (23013126655500984967/6250000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree059.table
  base := (-1161607693470344898948167796533197379823/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-47541417644981265379078294972560000000000000)
      constant := (475889040343037723605899939609315768075401885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree059.table
  base := (-5809630902377064831521397628123407397707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-243013092452672212801789710406680000000000000)
      constant := (2490649945666221846722741826709069086792820465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (368210026488015759471/100000000000000000000)
  centralHi := (23013126655500984967/6250000000000000000)
  directionLo := (371370685545151837141/100000000000000000000)
  directionHi := (185685342772575918571/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree060.table
  base := (-1112798467028817217534066164533088286437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-5377308250880735543270061470900000000000000)
      constant := (54932717525176523434178738466249687426098535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree060.table
  base := (-556542890953707213377761785359363197829/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-27486089754716207197299260523300000000000000)
      constant := (287455072013324725255127384425157201791370950) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (371370685545151837141/100000000000000000000)
  centralHi := (185685342772575918571/50000000000000000000)
  directionLo := (1462908870871730631/390625000000000000)
  directionHi := (374504670943163041537/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree061.table
  base := (-5309920847908086032443214636500280813069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-49250130870871974399782811503640000000000000)
      constant := (513244240777116736183558825691492769605207531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree061.table
  base := (-165975514294271752179066738494973192027/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-251736523132219516749596979012720000000000000)
      constant := (2685330698902282414103109772789105956406043680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1462908870871730631/390625000000000000)
  centralHi := (374504670943163041537/100000000000000000000)
  directionLo := (188806323407227021171/50000000000000000000)
  directionHi := (377612646814454042343/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree062.table
  base := (-100916788244094176165892382374346570641/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-50104487483817328910135069769180000000000000)
      constant := (532438349422156678803259908360536228488137950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree062.table
  base := (-1261751893945508987736866032077223269737/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-256098238471993168723500613315740000000000000)
      constant := (2785354915556193385596683251880478845508281260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188806323407227021171/50000000000000000000)
  centralHi := (377612646814454042343/100000000000000000000)
  directionLo := (23793453136297249001/6250000000000000000)
  directionHi := (380695250180755984017/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree063.table
  base := (-4771761717518279137496306125603564572017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-5662093788529187046720814226080000000000000)
      constant := (61330749783928867796009226846130569838687087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree063.table
  base := (-4772814698332876034791905078809964337363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-28939994867974091188600471957640000000000000)
      constant := (320796459597932194167763351447373601532510465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23793453136297249001/6250000000000000000)
  centralHi := (380695250180755984017/100000000000000000000)
  directionLo := (383753092477649187673/100000000000000000000)
  directionHi := (191876546238824593837/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree064.table
  base := (-89753998561449200937606944510254925407/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-51813200709708037930839586300260000000000000)
      constant := (571859405037580382733238007306121346950819650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree064.table
  base := (-4488648844744020484713120084484518496969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-264821669151540472671307881921780000000000000)
      constant := (2990770218067000671697007657103902836946918155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383753092477649187673/100000000000000000000)
  centralHi := (191876546238824593837/50000000000000000000)
  directionLo := (386786760970602443937/100000000000000000000)
  directionHi := (193393380485301221969/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree065.table
  base := (-2096832426604056138285417361551148991577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-52667557322653392441191844565800000000000000)
      constant := (592086292253722817725662041348960922945816446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree065.table
  base := (-262157486370827025428719196838986918973/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-269183384491314124645211516224800000000000000)
      constant := (3096161033594260648962635818069893601900098160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386786760970602443937/100000000000000000000)
  centralHi := (193393380485301221969/50000000000000000000)
  directionLo := (389796820071817325861/100000000000000000000)
  directionHi := (194898410035908662931/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree066.table
  base := (-972416524679839459325845904287379145441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-5946879326177638550171566981260000000000000)
      constant := (68073042746568511532381312125763789707870204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree066.table
  base := (-1945218083463279177048172136392834191681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-30393899981231975179901683391980000000000000)
      constant := (355926718930949549320749078393920709186041910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389796820071817325861/100000000000000000000)
  centralHi := (194898410035908662931/50000000000000000000)
  directionLo := (196391906283120226093/50000000000000000000)
  directionHi := (392783812566240452187/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree067.table
  base := (-223482012579767293917674105528745660731/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-54376270548544101461896361096880000000000000)
      constant := (633572660229882862919201247232985720583018704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree067.table
  base := (-3576405673421227806246301924282008420679/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-277906815170861428593018784830840000000000000)
      constant := (3312308428623424087084231490071478480489069605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196391906283120226093/50000000000000000000)
  centralHi := (392783812566240452187/100000000000000000000)
  directionLo := (395748260754285932751/100000000000000000000)
  directionHi := (24734266297142870797/6250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree068.table
  base := (-3251810747824725443408996434797289217937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2592)
      previous := (1539)
      next := (0)
      square := (67449206285159566606757231490000000000000)
      linear := (-3248860421264085645426389374260000000000000)
      constant := (38519535238375024833445868906036014749655639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree068.table
  base := (-101638596997081899819176921993429359027/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (12798)
      previous := (7857)
      next := (0)
      square := (337246031425797833033786157450000000000000)
      linear := (-16604031206507945915701318772580000000000000)
      constant := (201356754109560040661952646590768849291019040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395748260754285932751/100000000000000000000)
  centralHi := (24734266297142870797/6250000000000000000)
  directionLo := (4983633343976013499/1250000000000000000)
  directionHi := (398690667518081079921/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree069.table
  base := (-2917968481642438777680887710648329953427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-6231664863826090053622319736440000000000000)
      constant := (75159520405258765948614679549692632643459597) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree069.table
  base := (-5837060977982927502109352650377890107/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-31847805094489859171202894826320000000000000)
      constant := (392845507296418807681303959679227974397692500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4983633343976013499/1250000000000000000)
  centralHi := (398690667518081079921/100000000000000000000)
  directionLo := (80322303463479893497/20000000000000000000)
  directionHi := (200805758658699733743/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree070.table
  base := (-3217739245678597580401533100440464249/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-56939340387380164992953135893500000000000000)
      constant := (698383398424834464031760263992603481990680800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree070.table
  base := (-2574697175397317201056116936989449843927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-290991961190182384514729687739900000000000000)
      constant := (3649942596505055926101503974298052204779729365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80322303463479893497/20000000000000000000)
  centralHi := (200805758658699733743/50000000000000000000)
  directionLo := (20225563856043336081/5000000000000000000)
  directionHi := (404511277120866721621/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree071.table
  base := (-2220484820551579116101126925736798666571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-57793697000325519503305394159040000000000000)
      constant := (720675229526697715002246547551788586668248829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree071.table
  base := (-2220939903911790790942493730346572494991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-295353676529956036488633322042920000000000000)
      constant := (3766063850720437798706847745961096824702642045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20225563856043336081/5000000000000000000)
  centralHi := (404511277120866721621/100000000000000000000)
  directionLo := (40739039727750752827/10000000000000000000)
  directionHi := (407390397277507528271/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree072.table
  base := (-464213372557919286287216933002856790379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-6516450401474541557073072491620000000000000)
      constant := (82590129403679770195805034862728697550321876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree072.table
  base := (-1857262878447310072304441660672988993601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-33301710207747743162504106260660000000000000)
      constant := (431552585960225976961036749389671530904246555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40739039727750752827/10000000000000000000)
  centralHi := (407390397277507528271/100000000000000000000)
  directionLo := (410249312333239863739/100000000000000000000)
  directionHi := (20512465616661993187/5000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree073.table
  base := (-296660323340752894511108805075333282599/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-59502410226216228524009910690120000000000000)
      constant := (766291192790970453684598624207665290659800005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree073.table
  base := (-296733965444098871889514530985260249643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-304077107209503340436440590648960000000000000)
      constant := (4003670816784386773746408486825809452266963925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410249312333239863739/100000000000000000000)
  centralHi := (20512465616661993187/5000000000000000000)
  directionLo := (413088441796507995979/100000000000000000000)
  directionHi := (20654422089825399799/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree074.table
  base := (-549916472144207906248775616948877817043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-60356766839161583034362168955660000000000000)
      constant := (789615304261277465937733674372711937595742314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree074.table
  base := (-1100164056951363030135664177860153304597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-308438822549276992410344224951980000000000000)
      constant := (4125156437143602889990263046988272706273716015) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (413088441796507995979/100000000000000000000)
  centralHi := (20654422089825399799/5000000000000000000)
  directionLo := (51988523857109223729/12500000000000000000)
  directionHi := (415908190856873789833/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree075.table
  base := (-141290160519190550155622120391708749409/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-6801235939122993060523825246800000000000000)
      constant := (90364832264858058008552920644783980857103995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree075.table
  base := (-176687125219741395537836130861500159733/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-34755615321005627153805317695000000000000000)
      constant := (472047788508100922518025704892370529076743260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51988523857109223729/12500000000000000000)
  centralHi := (415908190856873789833/100000000000000000000)
  directionLo := (418708951060051420031/100000000000000000000)
  directionHi := (3271163680156651719/781250000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree076.table
  base := (-151579076397926861872625081396335463507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-62065480065052292055066685486740000000000000)
      constant := (837295743456303808689385237584256262918836586) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree076.table
  base := (-303425761299119877191973753257335771931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-317162253228824296358151493558020000000000000)
      constant := (4373491761229445900470939210354232348286037345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418708951060051420031/100000000000000000000)
  centralHi := (3271163680156651719/781250000000000000)
  directionLo := (21074555047128475237/5000000000000000000)
  directionHi := (421491100942569504741/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree077.table
  base := (110042371283648080365270958851472634121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-62919836677997646565418943752280000000000000)
      constant := (861652056628434091252359320232842680321348721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree077.table
  base := (549009263752965945272493872100872063/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-321523968568597948332055127861040000000000000)
      constant := (4500341401084181943867964864552460368235863000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21074555047128475237/5000000000000000000)
  centralHi := (421491100942569504741/100000000000000000000)
  directionLo := (424255006628973202641/100000000000000000000)
  directionHi := (212127503314486601321/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree078.table
  base := (533148426647950383517347697387085869307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-7086021476771444563974578001980000000000000)
      constant := (98483602645109378804525180497024867816229723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree078.table
  base := (532932292104775786086542294690642439123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-36209520434263511145106529129340000000000000)
      constant := (514330998831968937118626211003171978324532735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424255006628973202641/100000000000000000000)
  centralHi := (212127503314486601321/50000000000000000000)
  directionLo := (213500511197116853991/50000000000000000000)
  directionHi := (427001022394233707983/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree079.table
  base := (96615792870720916765415324490389126383/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-64628549903888355586123460283360000000000000)
      constant := (911396839566936578363521343778025021177221830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree079.table
  base := (482981868946250347054277678530492825331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-330247399248145252279862396467080000000000000)
      constant := (4759404502785644962576510516918832118386859310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213500511197116853991/50000000000000000000)
  centralHi := (427001022394233707983/100000000000000000000)
  directionLo := (107432372798452741639/25000000000000000000)
  directionHi := (429729491193810966557/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree080.table
  base := (1409069022470333578381505330748220345253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-65482906516833710096475718548900000000000000)
      constant := (936785299086458771308464210061276121118003053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree080.table
  base := (1408894575333331615143496766652689044227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-334609114587918904253766030770100000000000000)
      constant := (4891617919977735955339397297483918221020172135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107432372798452741639/25000000000000000000)
  centralHi := (429729491193810966557/100000000000000000000)
  directionLo := (432440745163614800563/100000000000000000000)
  directionHi := (108110186290903700141/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree081.table
  base := (18618800569569299271297537667498781317/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-7370807014419896067425330757160000000000000)
      constant := (106946422007816776010176173687060714780061300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree081.table
  base := (1861723370522068457583521513653548356829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-37663425547521395136407740563680000000000000)
      constant := (558402135824006253907215135152355377375617905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432440745163614800563/100000000000000000000)
  centralHi := (108110186290903700141/25000000000000000000)
  directionLo := (435135106091927749429/100000000000000000000)
  directionHi := (43513510609192774943/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree082.table
  base := (1162294781233768300636660980216997809739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-67191619742724419117180235079980000000000000)
      constant := (988594332695924917058446278427808822606262278) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree082.table
  base := (1162224424930575049302476140509803426037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-343332545267466208201573299376140000000000000)
      constant := (5161408393537469669650805350072515987111222370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435135106091927749429/100000000000000000000)
  centralHi := (43513510609192774943/10000000000000000000)
  directionLo := (437812885865187844703/100000000000000000000)
  directionHi := (13681652683287120147/3125000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree083.table
  base := (2797196230392693094815010733389712520037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-68045976355669773627532493345520000000000000)
      constant := (1015014899559487363432947640731016642264616237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree083.table
  base := (2797069881838572790415787657723362470849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-347694260607239860175476933679160000000000000)
      constant := (5298985418626662500056969720237458328933391245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437812885865187844703/100000000000000000000)
  centralHi := (13681652683287120147/3125000000000000000)
  directionLo := (440474386889379504283/100000000000000000000)
  directionHi := (110118596722344876071/25000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree084.table
  base := (102490590477409197550610768222449233207/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-7655592552068347570876083512340000000000000)
      constant := (115753277292187674965116866501241210508698336) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree084.table
  base := (819896365220916412618623976514924550199/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-39117330660779279127708951998020000000000000)
      constant := (604261142734020911283997411846352263900150220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440474386889379504283/100000000000000000000)
  centralHi := (110118596722344876071/25000000000000000000)
  directionLo := (443119902488644217069/100000000000000000000)
  directionHi := (44311990248864421707/10000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree085.table
  base := (3772096518886798085910858050064502228671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (2592)
      previous := (1539)
      next := (0)
      square := (67449206285159566606757231490000000000000)
      linear := (-4103217034209440155778647639800000000000000)
      constant := (62875771659181386303914423853409868840986663) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree085.table
  base := (754398938612722502453935825902431282359/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7650000000000000000000000000000000000000000
      center := (12798)
      previous := (7857)
      next := (0)
      square := (337246031425797833033786157450000000000000)
      linear := (-20965746546281597889604953075600000000000000)
      constant := (328206057638261794111902681151026799655023175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443119902488644217069/100000000000000000000)
  centralHi := (44311990248864421707/10000000000000000000)
  directionLo := (445749717282598329489/100000000000000000000)
  directionHi := (44574971728259832949/10000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree086.table
  base := (4274388176055625149885268312815719528903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-70609046194505837158589268142140000000000000)
      constant := (1096340764882313608676900482702913686494676703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree086.table
  base := (4274296783410670914540592789029680825537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-360779406626560816097187836588220000000000000)
      constant := (5722443494020893904387380356357954999136108685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445749717282598329489/100000000000000000000)
  centralHi := (44574971728259832949/10000000000000000000)
  directionLo := (112091026885932957007/25000000000000000000)
  directionHi := (448364107543731828029/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree087.table
  base := (74790203782998656093810457815192121339/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-7940378089716799074326836267520000000000000)
      constant := (124904159279267578621599215044979793476286144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree087.table
  base := (1196622756173503007269140748869109650079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-40571235774037163119010163432360000000000000)
      constant := (651907979768886831788911247006717453777456620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112091026885932957007/25000000000000000000)
  centralHi := (448364107543731828029/100000000000000000000)
  directionLo := (11274083538403961463/2500000000000000000)
  directionHi := (450963341536158458521/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree088.table
  base := (5308650381709018022887835088570242420929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-72317759420396546179293784673220000000000000)
      constant := (1152278122186730736155654237386491200536836329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree088.table
  base := (5308576787471342327556555611244306308101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-369502837306108120044995105194260000000000000)
      constant := (6013687943361816217704993130715368203536853505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11274083538403961463/2500000000000000000)
  centralHi := (450963341536158458521/100000000000000000000)
  directionLo := (226773839918446436133/50000000000000000000)
  directionHi := (453547679836892872267/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree089.table
  base := (5840619538902674425569337483128829044463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-73172116033341900689646042938760000000000000)
      constant := (1180762829196170166758145067513048084344648263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree089.table
  base := (5840553511274281004375296746876249442311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-373864552645881772018898739497280000000000000)
      constant := (6161991863057506806824859492390299623997254555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226773839918446436133/50000000000000000000)
  centralHi := (453547679836892872267/100000000000000000000)
  directionLo := (114029343910185970863/25000000000000000000)
  directionHi := (456117375640743883453/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree090.table
  base := (6382479928335908351582355870414261982051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-8225163627365250577777589022700000000000000)
      constant := (134399061446579223091800811796549721712812739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree090.table
  base := (3191210348399066606643415037840026801581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-42025140887295047110311374866700000000000000)
      constant := (701342618945955077442707960672957677456569090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114029343910185970863/25000000000000000000)
  centralHi := (456117375640743883453/100000000000000000000)
  directionLo := (91734535009966719123/20000000000000000000)
  directionHi := (14333521095307299863/3125000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree091.table
  base := (6934231027407710998528240809551622296513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-74880829259232609710350559469840000000000000)
      constant := (1238764292296574035464802066158473769593230313) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree091.table
  base := (3467088949490731542383872836004047402799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-382587983325429075966706008103320000000000000)
      constant := (6463963059942058914700377645631279272946801990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91734535009966719123/20000000000000000000)
  centralHi := (14333521095307299863/3125000000000000000)
  directionLo := (461213817348679421243/100000000000000000000)
  directionHi := (115303454337169855311/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree092.table
  base := (7495872369315563693033100235368541264511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-75735185872177964220702817735380000000000000)
      constant := (1268281045814099898604483854220113575828993111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree092.table
  base := (7495824720873949349146480259549279576061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-386949698665202727940609642406340000000000000)
      constant := (6617630326180557531860798810705854380886673305) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (461213817348679421243/100000000000000000000)
  centralHi := (115303454337169855311/25000000000000000000)
  directionLo := (11593525881642731597/2500000000000000000)
  directionHi := (463741035265709263881/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree093.table
  base := (8067403536874167519000969093042047905479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-8509949165013702081228341777880000000000000)
      constant := (144237979165187959418276340582919151844683431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree093.table
  base := (1008420101025324063311220920198978217649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-43479046000552931101612586301040000000000000)
      constant := (752565040513530132218778112305634188196022440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11593525881642731597/2500000000000000000)
  centralHi := (463741035265709263881/100000000000000000000)
  directionLo := (466254555222018805341/100000000000000000000)
  directionHi := (233127277611009402671/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree094.table
  base := (4324412078511825934727093348545459549467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-77443899098068673241407334266460000000000000)
      constant := (1328346591344020520496062803794013480576327334) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree094.table
  base := (540549115284787888819070247007393203899/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-395673129344750031888416911012380000000000000)
      constant := (6930328171150777612729309504012482377867303920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (466254555222018805341/100000000000000000000)
  centralHi := (233127277611009402671/50000000000000000000)
  directionLo := (46875459756812344687/10000000000000000000)
  directionHi := (468754597568123446871/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree095.table
  base := (2310033473987557294354944382169436884249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-78298255711014027751759592532000000000000000)
      constant := (1358895381517836894337514360538840821343726596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree095.table
  base := (9240099547120417897951607379564034487777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-400034844684523683862320545315400000000000000)
      constant := (7089358742089560278543210831307580268513539885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46875459756812344687/10000000000000000000)
  centralHi := (468754597568123446871/100000000000000000000)
  directionLo := (471241376809405547513/100000000000000000000)
  directionHi := (235620688404702773757/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree096.table
  base := (9841332454750873344336947161098922833777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (4896)
      previous := (2907)
      next := (0)
      square := (127404056316412514701652548370000000000000)
      linear := (-8794734702662153584679094533060000000000000)
      constant := (154420909136743776156276123241877588698961553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree096.table
  base := (9841301662892257918880051797101339470473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (24174)
      previous := (14841)
      next := (0)
      square := (637020281582062573508262741850000000000000)
      linear := (-44932951113810815092913797735380000000000000)
      constant := (805575230460870130391853010088667435534833485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471241376809405547513/100000000000000000000)
  centralHi := (235620688404702773757/50000000000000000000)
  directionLo := (118428775455227446231/25000000000000000000)
  directionHi := (18948604072836391397/4000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree097.table
  base := (5226209782790623580340852112742765497221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-80006968936904736772464109063080000000000000)
      constant := (1421024992785928672621003148157757866116543642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree097.table
  base := (10452391965332952219267784883230055002627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-408758275364070987810127813921440000000000000)
      constant := (7412783164379448338969290428942652865309164135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell016.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118428775455227446231/25000000000000000000)
  centralHi := (18948604072836391397/4000000000000000000)
  directionLo := (238087988026047686147/50000000000000000000)
  directionHi := (95235195210419074459/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 19
  qDenominator := 51
  table := BinomialMassData.Q19_51.Degree098.table
  base := (11073394988232896890041643706289506882487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (44064)
      previous := (26163)
      next := (0)
      square := (1146636506847712632314872935330000000000000)
      linear := (-80861325549850091282816367328620000000000000)
      constant := (1452605812558758767812659812035979007401348687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q19_51.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 97
  qDenominator := 255
  table := BinomialMassData.Q97_255.Degree098.table
  base := (11073370251395853694415181191788875068453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (217566)
      previous := (133569)
      next := (0)
      square := (5733182534238563161574364676650000000000000)
      linear := (-413119990703844639784031448224460000000000000)
      constant := (7577177010143790129274432216814190320265231265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q97_255.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell016.Kernel098
