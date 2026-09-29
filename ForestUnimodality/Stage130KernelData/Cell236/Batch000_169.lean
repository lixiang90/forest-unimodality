import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell236.Parameters
import ForestUnimodality.BinomialMassData.Q9_14.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_14.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_14.Batch100_149
import ForestUnimodality.BinomialMassData.Q9_14.Batch150_199
import ForestUnimodality.BinomialMassData.Q41_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q41_63.Batch050_099
import ForestUnimodality.BinomialMassData.Q41_63.Batch100_149
import ForestUnimodality.BinomialMassData.Q41_63.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree000.table
  base := (883611773868679716391838491/100000000000000000000000000)
  polynomial :=
    { denominator := 5600000000000000000000000000000000000000
      center := (9)
      previous := (0)
      next := (5)
      square := (160739719399883829176189920800000000000)
      linear := (-357056943950345972993432040800000000000)
      constant := (49482259336646064117942955496000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree000.table
  base := (883611773868679716391838491/100000000000000000000000000)
  polynomial :=
    { denominator := 25200000000000000000000000000000000000000
      center := (41)
      previous := (0)
      next := (22)
      square := (723328737299477231292854643600000000000)
      linear := (-1606756247776556878470444183600000000000)
      constant := (222670167014907288530743299732000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree001.table
  base := (68253601457561147639343966557243543713781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-14093057436612058119784762760000000000000)
      constant := (962949539310082365772300713016409611992934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree001.table
  base := (68008582747487234686635920737402273872511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-63705793677968339805417485850000000000000)
      constant := (4318341210669216997420398896996343253968193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4767192831009906813/10000000000000000000)
  directionHi := (47671928310099068131/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree002.table
  base := (52603412216600778872387343470021195515243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-19259691274465466914733724500000000000000)
      constant := (754567416308054978938860360700296737213402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree002.table
  base := (52224182079660395279915809720059618291761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-87242681161522757649073867110000000000000)
      constant := (3373042123107389090952858454263755952380943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4767192831009906813/10000000000000000000)
  centralHi := (47671928310099068131/100000000000000000000)
  directionLo := (16854571890155001033/25000000000000000000)
  directionHi := (67418287560620004133/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree003.table
  base := (40404286381389645119806775485319639994793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-24426325112318875709682686240000000000000)
      constant := (597821588453708359389151969509474959927102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree003.table
  base := (19981649606702840727256657941394635102157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-110779568645077175492730248370000000000000)
      constant := (2665042313978346860101818554695724022871782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16854571890155001033/25000000000000000000)
  centralHi := (67418287560620004133/100000000000000000000)
  directionLo := (82570201927872714759/100000000000000000000)
  directionHi := (2064255048196817869/2500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree004.table
  base := (15437035380928572379391046025034651254947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-29592958950172284504631647980000000000000)
      constant := (481761911086054084403693151700970235138516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree004.table
  base := (30417455639065870819296487660794761300229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-134316456128631593336386629630000000000000)
      constant := (2143407637173685294225966249710069961914427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82570201927872714759/100000000000000000000)
  centralHi := (2064255048196817869/2500000000000000000)
  directionLo := (4767192831009906813/5000000000000000000)
  directionHi := (95343856620198136261/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree005.table
  base := (11699526263566130020292426397475009072329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-34759592788025693299580609720000000000000)
      constant := (397796404572897905500285742104300254025212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree005.table
  base := (22955042689754061644913519737968161799737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-157853343612186011180043010890000000000000)
      constant := (1768346746679529584376137804391994193383431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4767192831009906813/5000000000000000000)
  centralHi := (95343856620198136261/100000000000000000000)
  directionLo := (2664941807996954763/2500000000000000000)
  directionHi := (106597672319878190521/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree006.table
  base := (17518180500810207666967898565437447338931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-39926226625879102094529571460000000000000)
      constant := (339470352444572856503469512556124262745034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree006.table
  base := (4275748486615303286517597647909277789831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-181390231095740429023699392150000000000000)
      constant := (1510056458098310161078809862813138003037412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2664941807996954763/2500000000000000000)
  centralHi := (106597672319878190521/100000000000000000000)
  directionLo := (116771899414282672539/100000000000000000000)
  directionHi := (5838594970714133627/5000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree007.table
  base := (100591998154118886025551010454644472803/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-45092860463732510889478533200000000000000)
      constant := (301804249832786154239994662729722895262976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree007.table
  base := (6248847407459123949819299161934197548763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-204927118579294846867355773410000000000000)
      constant := (1345629051991075146676886805403708891144138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116771899414282672539/100000000000000000000)
  centralHi := (5838594970714133627/5000000000000000000)
  directionLo := (25225613365484356409/20000000000000000000)
  directionHi := (63064033413710891023/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree008.table
  base := (9197315761560155055544800110044468550169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-50259494301585919684427494940000000000000)
      constant := (280954780977013919658589962580622559702366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree008.table
  base := (8859497835567310110471650023100707818491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-228464006062849264711012154670000000000000)
      constant := (1257446738405679626076139578735344592564933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25225613365484356409/20000000000000000000)
  centralHi := (63064033413710891023/50000000000000000000)
  directionLo := (26967315024248001653/20000000000000000000)
  directionHi := (67418287560620004133/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree009.table
  base := (1567655898780122443988759847297480742589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-55426128139439328479376456680000000000000)
      constant := (273951469288616721225556011223658921584984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree009.table
  base := (5973021262439683660991598876767801654789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-252000893546403682554668535930000000000000)
      constant := (1231940467346094483869157533616371504251707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26967315024248001653/20000000000000000000)
  centralHi := (67418287560620004133/50000000000000000000)
  directionLo := (14301578493029720439/10000000000000000000)
  directionHi := (143015784930297204391/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree010.table
  base := (982861718662620524704837278851558197853/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-60592761977292737274325418420000000000000)
      constant := (278494781310986206309346235815687259079768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree010.table
  base := (28688322195729634658502936556252218417/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-275537781029958100398324917190000000000000)
      constant := (1258642167979955275216606322689617889314688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14301578493029720439/10000000000000000000)
  centralHi := (143015784930297204391/100000000000000000000)
  directionLo := (75375936956087401489/50000000000000000000)
  directionHi := (150751873912174802979/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree011.table
  base := (2052421048361861611467764625580950258577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-65759395815146146069274380160000000000000)
      constant := (292801613319086589132581131073133303620078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree011.table
  base := (114271376803017379863964333358952344279/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-299074668513512518241981298450000000000000)
      constant := (1329462152525971872330557189065823963033232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75375936956087401489/50000000000000000000)
  centralHi := (150751873912174802979/100000000000000000000)
  directionLo := (39527474809329993211/25000000000000000000)
  directionHi := (31621979847463994569/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree012.table
  base := (106923666888850515648878343650035936003/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-14185205930599910972844668380000000000000)
      constant := (63097395273514521879215635635100503104042) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree012.table
  base := (342325524170546084156382845577942237057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-322611555997066936085637679710000000000000)
      constant := (1438137836579955372820266419871410360934591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39527474809329993211/25000000000000000000)
  centralHi := (31621979847463994569/20000000000000000000)
  directionLo := (82570201927872714759/50000000000000000000)
  directionHi := (165140403855745429519/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree013.table
  base := (-174732819109167334720369372638281397423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-76092663490852963659172303640000000000000)
      constant := (345473290325763726367407466747256241744312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree013.table
  base := (-107879141651680147927700564380316943341/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-346148443480621353929294060970000000000000)
      constant := (1579812621947186555047077036532320260556136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82570201927872714759/50000000000000000000)
  centralHi := (165140403855745429519/100000000000000000000)
  directionLo := (171883581922305554791/100000000000000000000)
  directionHi := (21485447740288194349/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree014.table
  base := (-341642871708850054127808654818537783967/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-16251859465741274490824253076000000000000)
      constant := (76384148630794618843272038592540471024462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree014.table
  base := (-1847619465698947054820628785148496054341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-369685330964175771772950442230000000000000)
      constant := (1750713720716763829226652988715644748576517) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171883581922305554791/100000000000000000000)
  centralHi := (21485447740288194349/12500000000000000000)
  directionLo := (17837202270323995491/10000000000000000000)
  directionHi := (178372022703239954911/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree015.table
  base := (-2540059164442671683333974631035776501059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-86425931166559781249070227120000000000000)
      constant := (424173739316302172414656990840499128985174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree015.table
  base := (-2658034437752407416530969018193875036903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-393222218447730189616606823490000000000000)
      constant := (1947905272127301734510106696053785872675111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17837202270323995491/10000000000000000000)
  centralHi := (178372022703239954911/100000000000000000000)
  directionLo := (92316292213303788679/50000000000000000000)
  directionHi := (184632584426607577359/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree016.table
  base := (-403885228379271282886149268205424874697/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-91592565004413190044019188860000000000000)
      constant := (471719652952119647356576944200992414033936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree016.table
  base := (-3330602500622157007260723422030902253889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-416759105931284607460263204750000000000000)
      constant := (2169098835750155182358827971452053158004993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92316292213303788679/50000000000000000000)
  centralHi := (184632584426607577359/100000000000000000000)
  directionLo := (4767192831009906813/2500000000000000000)
  directionHi := (190687713240396272521/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree017.table
  base := (-1904979697967147101374752428938859458149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-96759198842266598838968150600000000000000)
      constant := (524157005366807844342292810484711935171828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree017.table
  base := (-1946842278178657713730804024180750218353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-440295993414839025303919586010000000000000)
      constant := (2412507674756229637944358703653225472487522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4767192831009906813/2500000000000000000)
  centralHi := (190687713240396272521/100000000000000000000)
  directionLo := (39311279159882256313/20000000000000000000)
  directionHi := (98278197899705640783/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree018.table
  base := (-537398311309302910851221364861353308317/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-101925832680120007633917112340000000000000)
      constant := (581170871889727446388876491575528429468496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree018.table
  base := (-873891914939566581067830496696755157013/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-92766576179678688629515193454000000000000)
      constant := (535346902810381647377950105744104425108181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39311279159882256313/20000000000000000000)
  centralHi := (98278197899705640783/50000000000000000000)
  directionLo := (202254862681860012397/100000000000000000000)
  directionHi := (101127431340930006199/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree019.table
  base := (-943287039906315408595429052743397128853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-21418493303594683285773214816000000000000)
      constant := (128502768655320036021685569276592440196058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree019.table
  base := (-2387649674691928566583580243443563678239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-487369768381947860991232348530000000000000)
      constant := (2960684930631561674581753809806110976541886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202254862681860012397/100000000000000000000)
  centralHi := (101127431340930006199/50000000000000000000)
  directionLo := (207797117947437555119/100000000000000000000)
  directionHi := (2597463974342969439/1250000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree020.table
  base := (-15861280129082824715604299767209680077/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-22451820071165365044763007164000000000000)
      constant := (141598252374523113474512480488580126651008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree020.table
  base := (-2562415591456860396936805041406591612819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-510906655865502278834888729790000000000000)
      constant := (3263500404437794991995905931382769456784806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207797117947437555119/100000000000000000000)
  centralHi := (2597463974342969439/1250000000000000000)
  directionLo := (213195344639756381041/100000000000000000000)
  directionHi := (106597672319878190521/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree021.table
  base := (-1077533028043446729934760458927954193747/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-23485146838736046803752799512000000000000)
      constant := (155489950627184238294773081658008641287542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree021.table
  base := (-2714380394728530986633032029950341136033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-534443543349056696678545111050000000000000)
      constant := (3584506475477920989726330437766257016859842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213195344639756381041/100000000000000000000)
  centralHi := (106597672319878190521/50000000000000000000)
  directionLo := (43692044001107444123/20000000000000000000)
  directionHi := (27307527500692152577/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree022.table
  base := (-5661245642042878732531861049659208828919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-122592368031533642813712959300000000000000)
      constant := (850768301825609477867148750424771076395134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree022.table
  base := (-5695510636589985946184944590001158479723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-557980430832611114522201492310000000000000)
      constant := (3923172528294645035458080732129927015777451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43692044001107444123/20000000000000000000)
  centralHi := (27307527500692152577/12500000000000000000)
  directionLo := (111800581923430691351/50000000000000000000)
  directionHi := (223601163846861382703/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree023.table
  base := (-2951590266669355808341141759767124334273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-127759001869387051608661921040000000000000)
      constant := (927851296529906612124806190241520518640356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree023.table
  base := (-5931715978369141019900058334210485285059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-581517318316165532365857873570000000000000)
      constant := (4279080541882398285833158994824739427041283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111800581923430691351/50000000000000000000)
  centralHi := (223601163846861382703/100000000000000000000)
  directionLo := (228626536566677173759/100000000000000000000)
  directionHi := (89307240846358271/39062500000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree024.table
  base := (-1223774504224615067331617266296177190431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-26585127141448092080722176556000000000000)
      constant := (201724619870111158352675098991853519333966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree024.table
  base := (-1228522192954986301103699396998749609779/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-121010841159943990041902850966000000000000)
      constant := (930380152958483053850363689845078774583923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228626536566677173759/100000000000000000000)
  centralHi := (89307240846358271/39062500000000000)
  directionLo := (233543798828565345079/100000000000000000000)
  directionHi := (5838594970714133627/2500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree025.table
  base := (-6312600956523675893156220845520769030407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-138092269545093869198559844520000000000000)
      constant := (1093023799371769132773099345537709233574302) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree025.table
  base := (-3166164846262735922564726268308180368323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-628591093283274368053170636090000000000000)
      constant := (5041372748931454775862439999693169273591302) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233543798828565345079/100000000000000000000)
  centralHi := (5838594970714133627/2500000000000000000)
  directionLo := (4767192831009906813/2000000000000000000)
  directionHi := (238359641550495340651/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree026.table
  base := (-6487759416242126701018335540038343800313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-143258903382947277993508806260000000000000)
      constant := (1181005886519724047346194663279463186795618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree026.table
  base := (-203254416310019656969307565901725092387/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-652127980766828785896827017350000000000000)
      constant := (5447290537200625185655073867682122213747808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4767192831009906813/2000000000000000000)
  centralHi := (238359641550495340651/100000000000000000000)
  directionLo := (243080092703791459279/100000000000000000000)
  directionHi := (3038501158797393241/1250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree027.table
  base := (-6647042082950893173500545886251393745161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-148425537220800686788457768000000000000000)
      constant := (1272531642237006019697075831587480487567746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree027.table
  base := (-666063399523853133361963431884172356143/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-135132973650076640748096679722000000000000)
      constant := (1173898215327280883216050806062594283125982) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243080092703791459279/100000000000000000000)
  centralHi := (3038501158797393241/1250000000000000000)
  directionLo := (247710605783618144277/100000000000000000000)
  directionHi := (123855302891809072139/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree028.table
  base := (-6792590182646799655725010570800167542353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-153592171058654095583406729740000000000000)
      constant := (1367571089359659508994032628848797654407058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree028.table
  base := (-85048236631397147892980299782242857263/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-139840351146787524316827955974000000000000)
      constant := (1261569028100547820940850802835499199878896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247710605783618144277/100000000000000000000)
  centralHi := (123855302891809072139/50000000000000000000)
  directionLo := (25225613365484356409/10000000000000000000)
  directionHi := (252256133654843564091/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree029.table
  base := (-1731526802530687128724322013284753659307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-158758804896507504378355691480000000000000)
      constant := (1466100378960583882096187236631053795078808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree029.table
  base := (-6935443485296616998681108962185119023221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-722738643217492039427796161130000000000000)
      constant := (6762250205273584463148039253962337501537077) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25225613365484356409/10000000000000000000)
  centralHi := (252256133654843564091/100000000000000000000)
  directionLo := (256721190623784550913/100000000000000000000)
  directionHi := (128360595311892275457/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree030.table
  base := (-7048949725611096644226397183595421746263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-163925438734360913173304653220000000000000)
      constant := (1568100519196526142498613391029664095552318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree030.table
  base := (-7056680002720787488945183634939945454419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-746275530701046457271452542390000000000000)
      constant := (7232624853331894090234967603898783436371603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256721190623784550913/100000000000000000000)
  centralHi := (128360595311892275457/50000000000000000000)
  directionLo := (5222198099042078653/2000000000000000000)
  directionHi := (261109904952103932651/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree031.table
  base := (-3581099500589887864485781626821809089393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-169092072572214321968253614960000000000000)
      constant := (1673556372258535246607681937963989345496996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree031.table
  base := (-7168595725833565584636475531896326118927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-769812418184600875115108923650000000000000)
      constant := (7718904368365563202173471929530531454507599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5222198099042078653/2000000000000000000)
  centralHi := (261109904952103932651/100000000000000000000)
  directionLo := (265426063552357221791/100000000000000000000)
  directionHi := (8294564486011163181/3125000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree032.table
  base := (-7266717631605760537758343559538497748729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-174258706410067730763202576700000000000000)
      constant := (1782455861819733547662635075286461031517794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree032.table
  base := (-363600394453901515901065413890458183809/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-158669861133631058591753060982000000000000)
      constant := (1644207452920935563986154768499604537680132) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265426063552357221791/100000000000000000000)
  centralHi := (8294564486011163181/3125000000000000000)
  directionLo := (26967315024248001653/10000000000000000000)
  directionHi := (269673150242480016531/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree033.table
  base := (-7363194322546132179220358599746487703273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-179425340247921139558151538440000000000000)
      constant := (1894789346000921910142602116018549172154178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree033.table
  base := (-7367567186118158062623600541462837162529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-816886193151709710802421686170000000000000)
      constant := (8738982548348407431974866466667841258760673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26967315024248001653/10000000000000000000)
  centralHi := (269673150242480016531/100000000000000000000)
  directionLo := (273854378658633875041/100000000000000000000)
  directionHi := (136927189329316937521/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree034.table
  base := (-1863044842179156800750185537676989968713/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-184591974085774548353100500180000000000000)
      constant := (2010549120676080022352579187290088561752072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree034.table
  base := (-7455792109201550528570602500634402701097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-840423080635264128646078067430000000000000)
      constant := (9272707554585153130567733040840032629830889) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273854378658633875041/100000000000000000000)
  centralHi := (136927189329316937521/50000000000000000000)
  directionLo := (277972720710701484089/100000000000000000000)
  directionHi := (27797272071070148409/10000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree035.table
  base := (-7534112790392724784579975386823671228293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-189758607923627957148049461920000000000000)
      constant := (2129729025561351175835839552659468602803898) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree035.table
  base := (-7537096109319441944598563851854165099837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-863959968118818546489734448690000000000000)
      constant := (9822186235902467159298989834133187598710269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277972720710701484089/100000000000000000000)
  centralHi := (27797272071070148409/10000000000000000000)
  directionLo := (70507732824187835133/25000000000000000000)
  directionHi := (282030931296751340533/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree036.table
  base := (-951168334064745224456359634509955213417/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-194925241761481365942998423660000000000000)
      constant := (2252324131467525854388683749374885016097296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree036.table
  base := (-1522361820476980766437260788234933193539/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-177499371120474592866678165990000000000000)
      constant := (2077479561519565202463094245549199208807043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70507732824187835133/25000000000000000000)
  centralHi := (282030931296751340533/100000000000000000000)
  directionLo := (286031569860594408781/100000000000000000000)
  directionHi := (143015784930297204391/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree037.table
  base := (-191954072996815781709313811815780803721/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-40018375119866954947589477080000000000000)
      constant := (475666098345535991112176860775632549983248) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree037.table
  base := (-7680194516711982181883773637979314317973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-911033743085927382177047211210000000000000)
      constant := (10968325673687444792212530316907303197967701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286031569860594408781/100000000000000000000)
  centralHi := (143015784930297204391/50000000000000000000)
  directionLo := (72494254817933384961/25000000000000000000)
  directionHi := (57995403854346707969/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree038.table
  base := (-3870393691606436292179755998060877646421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-205258509437188183532896347140000000000000)
      constant := (2507744944431227528009838070294295425900212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree038.table
  base := (-7742462819925908566453589514225005693257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-934570630569481800020703592470000000000000)
      constant := (11564956574710933909906122257583824641324809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72494254817933384961/25000000000000000000)
  centralHi := (57995403854346707969/20000000000000000000)
  directionLo := (293869502423307869459/100000000000000000000)
  directionHi := (14693475121165393473/5000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree039.table
  base := (-7797401108912595578152593006014173117129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-210425143275041592327845308880000000000000)
      constant := (2640564954928933834051973325590801576360194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree039.table
  base := (-7798782262678808115865522547098852972901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-958107518053036217864359973730000000000000)
      constant := (12177279910877209482208151478212772262707237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293869502423307869459/100000000000000000000)
  centralHi := (14693475121165393473/5000000000000000000)
  directionLo := (148855548438180307181/50000000000000000000)
  directionHi := (297711096876360614363/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree040.table
  base := (-7848149305976126520010483714124094164347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-215591777112895001122794270620000000000000)
      constant := (2776788490294738305903668434802262681699142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree040.table
  base := (-1962321854891095526194766605512670664493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-981644405536590635708016354990000000000000)
      constant := (12805287203986868328815069876610806992547764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (148855548438180307181/50000000000000000000)
  centralHi := (297711096876360614363/100000000000000000000)
  directionLo := (301503747824349605957/100000000000000000000)
  directionHi := (150751873912174802979/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree041.table
  base := (-7893148499703576101106692211279420433919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-220758410950748409917743232360000000000000)
      constant := (2916413919174439393888494284657088113925134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree041.table
  base := (-986760748085056626561205270860017887931/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1005181293020145053551672736250000000000000)
      constant := (13448971669311747633531265928026550984482776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301503747824349605957/100000000000000000000)
  centralHi := (150751873912174802979/50000000000000000000)
  directionLo := (152624639803778263283/50000000000000000000)
  directionHi := (305249279607556526567/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree042.table
  base := (-7932492243316953990134468884231251761609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-225925044788601818712692194100000000000000)
      constant := (3059439931822928962644745369740762475337474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree042.table
  base := (-3966632091426569312100518990884989478933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1028718180503699471395329117510000000000000)
      constant := (14108327874687801975888900975848491325654442) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152624639803778263283/50000000000000000000)
  centralHi := (305249279607556526567/100000000000000000000)
  directionLo := (154474702985420439467/50000000000000000000)
  directionHi := (61789881194168175787/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree043.table
  base := (-7966255681696212794524808942707619492341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-231091678626455227507641155840000000000000)
      constant := (3205865476211887675668387757117093327107226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree043.table
  base := (-7966891081782897674759497297432616935103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1052255067987253889238985498770000000000000)
      constant := (14783351468849902455592661683941745133088511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154474702985420439467/50000000000000000000)
  centralHi := (61789881194168175787/20000000000000000000)
  directionLo := (312605739228406801061/100000000000000000000)
  directionHi := (156302869614203400531/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree044.table
  base := (-31228512502041816994765104229079266541/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-236258312464308636302590117580000000000000)
      constant := (3355689706941776596050071286642979908717056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree044.table
  base := (-3997511015390233394007469568312971948751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1075791955470808307082641880030000000000000)
      constant := (15474038964791472665340003153872565534457374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312605739228406801061/100000000000000000000)
  centralHi := (156302869614203400531/50000000000000000000)
  directionLo := (316219798474639945689/100000000000000000000)
  directionHi := (31621979847463994569/10000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree045.table
  base := (-8017271346071303302126048761646124628593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-241424946302162045097539079320000000000000)
      constant := (3508911944364747512379586265111954255199698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree045.table
  base := (-4008850702408797844938831439632639271469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1099328842954362724926298261290000000000000)
      constant := (16180387566889292372398576524706287451794906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316219798474639945689/100000000000000000000)
  centralHi := (31621979847463994569/10000000000000000000)
  directionLo := (159896508479817285781/50000000000000000000)
  directionHi := (319793016959634571563/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree046.table
  base := (-8034611162891520143684067825176703760143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-246591580140015453892488041060000000000000)
      constant := (3665531641857107244130282715487526147357998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree046.table
  base := (-8034964795589894632416992494688974711631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1122865730437917142769954642550000000000000)
      constant := (16902395032866538130888014386374594593167247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159896508479817285781/50000000000000000000)
  centralHi := (319793016959634571563/100000000000000000000)
  directionLo := (40415843591372900653/12500000000000000000)
  directionHi := (12933069949239328209/4000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree047.table
  base := (-8046550066530743290288692636782929212431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-251758213977868862687437002800000000000000)
      constant := (3825548359601192364692793875080038991025966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree047.table
  base := (-8046840762045856424123381086223666835453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1146402617921471560613611023810000000000000)
      constant := (17640059563509454893873418193367908989366461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40415843591372900653/12500000000000000000)
  centralHi := (12933069949239328209/4000000000000000000)
  directionLo := (65364454925823889931/20000000000000000000)
  directionHi := (40852784328639931207/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree048.table
  base := (-1006639168075321809231630089389028810163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-256924847815722271482385964540000000000000)
      constant := (3988961743570412449820336098628428773261744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree048.table
  base := (-322134089188517659209162641290981474863/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25200000000000000000000000000000000000000
      center := (41)
      previous := (0)
      next := (22)
      square := (723328737299477231292854643600000000000)
      linear := (-46797580216201039138290696202800000000000)
      constant := (735735188580392506207806279633868167083631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65364454925823889931/20000000000000000000)
  centralHi := (40852784328639931207/12500000000000000000)
  directionLo := (82570201927872714759/25000000000000000000)
  directionHi := (330280807711490859037/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree049.table
  base := (-8054321360575677053592825375328838577387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-262091481653575680277334926280000000000000)
      constant := (4155771508676206212483889399720396259916582) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree049.table
  base := (-805451760984677966584121271448007398279/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-238695278577716079260184757266000000000000)
      constant := (3832470865191701346670295871953551067816846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82570201927872714759/25000000000000000000)
  centralHi := (330280807711490859037/100000000000000000000)
  directionLo := (333703498170693476911/100000000000000000000)
  directionHi := (20856468635668342307/6250000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree050.table
  base := (-8050190519621140211894540143162548698631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-267258115491429089072283888020000000000000)
      constant := (4325977425246178404130042868995724318219166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree050.table
  base := (-8050351694923270229208998971259971557351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1217013280372134814144580167590000000000000)
      constant := (19946982465929555475702687096310621791886887) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333703498170693476911/100000000000000000000)
  centralHi := (20856468635668342307/6250000000000000000)
  directionLo := (337091437803100020663/100000000000000000000)
  directionHi := (42136429725387502583/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree051.table
  base := (-2010183510974315702669055018607228845381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-272424749329282497867232849760000000000000)
      constant := (4499579308170112840691944015672995184658664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree051.table
  base := (-2010216593871386595665740286280320607533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1240550167855689231988236548850000000000000)
      constant := (20747263385318741489871956410897359206901684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337091437803100020663/100000000000000000000)
  centralHi := (42136429725387502583/12500000000000000000)
  directionLo := (340445664077198190829/100000000000000000000)
  directionHi := (34044566407719819083/10000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree052.table
  base := (-4012981297565183892956603755048796420397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-277591383167135906662181811500000000000000)
      constant := (4676577008183841001065938046978633700228884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree052.table
  base := (-501629450888733704229681252744334935661/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1264087055339243649831892930110000000000000)
      constant := (21563196481676838513946563852633710384853712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340445664077198190829/100000000000000000000)
  centralHi := (34044566407719819083/10000000000000000000)
  directionLo := (171883581922305554791/50000000000000000000)
  directionHi := (343767163844611109583/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree053.table
  base := (-200147119369110157659757577575062615219/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-56551603400997863091426154648000000000000)
      constant := (971394080973429513777807550754592987095472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree053.table
  base := (-200149347646763785439433288151390400833/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-257524788564559613535109862274000000000000)
      constant := (4478956254046986057665312184487699237980168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (171883581922305554791/50000000000000000000)
  centralHi := (343767163844611109583/100000000000000000000)
  directionLo := (347056876731424131373/100000000000000000000)
  directionHi := (173528438365712065687/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree054.table
  base := (-3990253762951173078795069208280282773921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-287924650842842724252079734980000000000000)
      constant := (5040759401016590995164486294168152082330212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree054.table
  base := (-798058064583006408295758570287595819101/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-262232166061270497103841138526000000000000)
      constant := (4648403472136663138844989164659762926793274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (347056876731424131373/100000000000000000000)
  centralHi := (173528438365712065687/50000000000000000000)
  directionLo := (350315698242848017619/100000000000000000000)
  directionHi := (17515784912142400881/5000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree055.table
  base := (-993729557054203923384061448642833111519/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-293091284680696133047028696720000000000000)
      constant := (5227943918121719063226446774227002691509872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree055.table
  base := (-1589979285126689140656854583267276267433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-266939543557981380672572414778000000000000)
      constant := (4820980887711055823991039220734161595151721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (350315698242848017619/100000000000000000000)
  centralHi := (17515784912142400881/5000000000000000000)
  directionLo := (1104826508157155041/312500000000000000)
  directionHi := (353544482610289613121/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree056.table
  base := (-7913876098884904329153418068303015872037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-298257918518549541841977658460000000000000)
      constant := (5418523892727158780394494417683757777791482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree056.table
  base := (-3956962634965192569471488605249634399009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1358234605273461321206518455150000000000000)
      constant := (24983442250297890167313019968778546065724866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1104826508157155041/312500000000000000)
  centralHi := (353544482610289613121/100000000000000000000)
  directionLo := (356744045406479909821/100000000000000000000)
  directionHi := (178372022703239954911/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree057.table
  base := (-246019691232748286414015648282931366179/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-303424552356402950636926620200000000000000)
      constant := (5612499273506225224128811064064246747951808) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree057.table
  base := (-7872670426579025358689498908851336849617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1381771492757015739050174836410000000000000)
      constant := (25877630591296085829266801998242365778474129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356744045406479909821/100000000000000000000)
  centralHi := (178372022703239954911/50000000000000000000)
  directionLo := (359915165951344462987/100000000000000000000)
  directionHi := (89978791487836115747/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree058.table
  base := (-7826101486172459252045934247415797788791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-308591186194256359431875581940000000000000)
      constant := (5809870018906222519435761988576178830956926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree058.table
  base := (-3913067259588903060072123397498279177229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1405308380240570156893831217670000000000000)
      constant := (26787469296263164401086456438695216823669146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (359915165951344462987/100000000000000000000)
  centralHi := (89978791487836115747/25000000000000000000)
  directionLo := (90764647382181189203/25000000000000000000)
  directionHi := (363058589528724756813/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree059.table
  base := (-7774292604337228200334342745171674007943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-313757820032109768226824543680000000000000)
      constant := (6010636095253247723764306452842596563888798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree059.table
  base := (-3887159834744683228856820691285893993621/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1428845267724124574737487598930000000000000)
      constant := (27712958231528079623604378797777977356803754) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90764647382181189203/25000000000000000000)
  centralHi := (363058589528724756813/100000000000000000000)
  directionLo := (366175029431814581001/100000000000000000000)
  directionHi := (183087514715907290501/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree060.table
  base := (-3768166711636746607789714557201988989/4882812500000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-318924453869963177021773505420000000000000)
      constant := (6214797475226443566517489928415904571707392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree060.table
  base := (-3858613797861921621341005412217002166993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1452382155207678992581143980190000000000000)
      constant := (28654097288843592873929656401860657726958882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366175029431814581001/100000000000000000000)
  centralHi := (183087514715907290501/50000000000000000000)
  directionLo := (369265168853215154717/100000000000000000000)
  directionHi := (184632584426607577359/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree061.table
  base := (-1913710383728984323410271265238353431051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-324091087707816585816722467160000000000000)
      constant := (6422354136629384166914577995961652207861144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree061.table
  base := (-956857461432568995056389913147820727077/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1475919042691233410424800361450000000000000)
      constant := (29610886380414207276481978107313498353553192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (369265168853215154717/100000000000000000000)
  centralHi := (184632584426607577359/50000000000000000000)
  directionLo := (4654120782922456367/1250000000000000000)
  directionHi := (372329662633796509361/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree062.table
  base := (-948400277862623020153018214348404180003/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-329257721545669994611671428900000000000000)
      constant := (6633306061400499911620398899112978731839664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree062.table
  base := (-3793608544518376232993181101450561437/5000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25200000000000000000000000000000000000000
      center := (41)
      previous := (0)
      next := (22)
      square := (723328737299477231292854643600000000000)
      linear := (-59978237206991513130738269708400000000000)
      constant := (1223333017396107018415940960212689170357520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4654120782922456367/1250000000000000000)
  centralHi := (372329662633796509361/100000000000000000000)
  directionLo := (18768456944152331513/5000000000000000000)
  directionHi := (375369138883046630261/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree063.table
  base := (-1878572135274203748541033039539845619901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-334424355383523403406620390640000000000000)
      constant := (6847653234815856157893690030900768645285544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree063.table
  base := (-1878575177617983205681577977146712515663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1522992817658342246112113123970000000000000)
      constant := (31571414394221769677682664035239028446052924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18768456944152331513/5000000000000000000)
  centralHi := (375369138883046630261/100000000000000000000)
  directionLo := (75676840096453069227/20000000000000000000)
  directionHi := (47298025060283168267/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree064.table
  base := (-7436101348696057525579091222058477788791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-339590989221376812201569352380000000000000)
      constant := (7065395644846756117470798735691181310956926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree064.table
  base := (-1859027827096881537712292707365347493459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1546529705141896663955769505230000000000000)
      constant := (32575153210956339641763171445423932431648332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75676840096453069227/20000000000000000000)
  centralHi := (47298025060283168267/12500000000000000000)
  directionLo := (381375426480792545041/100000000000000000000)
  directionHi := (190687713240396272521/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree065.table
  base := (-7352641349356615655395780340194406750627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-344757623059230220996518314120000000000000)
      constant := (7286533281641989135752750409412278305491222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree065.table
  base := (-3676324749447359658272841401885709880461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1570066592625451081799425886490000000000000)
      constant := (33594541846291380580070029374062400555061914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (381375426480792545041/100000000000000000000)
  centralHi := (190687713240396272521/50000000000000000000)
  directionLo := (24021460837151824769/6250000000000000000)
  directionHi := (76868674678885839261/20000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree066.table
  base := (-7263909121014596279327403989012685008599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-349924256897083629791467275860000000000000)
      constant := (7511066137110449716199560189393822409879614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree066.table
  base := (-726391578803270550249581536097200912729/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-318720696021801099928616453550000000000000)
      constant := (6925916053669284664418879973359752684996146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24021460837151824769/6250000000000000000)
  centralHi := (76868674678885839261/20000000000000000000)
  directionLo := (193644288207148553623/50000000000000000000)
  directionHi := (387288576414297107247/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree067.table
  base := (-1433981027984590452724089780348835048461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-71018178146987407717283247520000000000000)
      constant := (1547798840916919303736755452274116309321546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree067.table
  base := (-3584955296513487453868383459101284462223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1617140367592559917486738649010000000000000)
      constant := (35680268450836261985296939423353238157759902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193644288207148553623/50000000000000000000)
  centralHi := (387288576414297107247/100000000000000000000)
  directionLo := (15608462021342965081/4000000000000000000)
  directionHi := (195105775266787063513/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree068.table
  base := (-3535314900019272299806344218869888519713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-360257524572790447381365199340000000000000)
      constant := (7970317478549033489326672798311643121448036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree068.table
  base := (-707063425938653902937208729035306554417/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-328135451015222867066079006054000000000000)
      constant := (7349321274398765769072024881077551374143458) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15608462021342965081/4000000000000000000)
  centralHi := (195105775266787063513/50000000000000000000)
  directionLo := (393112791598822563131/100000000000000000000)
  directionHi := (98278197899705640783/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree069.table
  base := (-6966083428661352529372031134811047162639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-365424158410643856176314161080000000000000)
      constant := (8205035954421560918739296080687645339723054) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree069.table
  base := (-1393217414931593832974673650334039786543/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-332842828511933750634810282306000000000000)
      constant := (7565718802740737982108648906224955493447791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393112791598822563131/100000000000000000000)
  centralHi := (98278197899705640783/25000000000000000000)
  directionLo := (395992777291988653469/100000000000000000000)
  directionHi := (39599277729198865347/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree070.table
  base := (-6856266299053450910230399488444180922593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-370590792248497264971263122820000000000000)
      constant := (8443149628376509758919000193561781467083698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree070.table
  base := (-3428134639746453584710585214888606347037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1687751030043223171017707792790000000000000)
      constant := (38926231360804791743969924481024035600273338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (395992777291988653469/100000000000000000000)
  centralHi := (39599277729198865347/10000000000000000000)
  directionLo := (398851968048580336397/100000000000000000000)
  directionHi := (199425984024290168199/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree071.table
  base := (-3370589320311849919073745536839430498153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-375757426086350673766212084560000000000000)
      constant := (8684658497202155968522349370883495946051716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree071.table
  base := (-421323817284772831424310708322997393219/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1711287917526777588861364174050000000000000)
      constant := (40039518400529238573274435172050418627635248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398851968048580336397/100000000000000000000)
  centralHi := (199425984024290168199/50000000000000000000)
  directionLo := (401690807917020892529/100000000000000000000)
  directionHi := (40169080791702089253/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree072.table
  base := (-662082064715009053119536283777360282521/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-76184811984840816512232209260000000000000)
      constant := (1785912511637121534099266963078233912089412) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree072.table
  base := (-25862588428513057396332849065133151401/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1734824805010332006705020555310000000000000)
      constant := (41168455122050417453362256985077532534204672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (401690807917020892529/100000000000000000000)
  centralHi := (40169080791702089253/10000000000000000000)
  directionLo := (80901945072744004959/20000000000000000000)
  directionHi := (101127431340930006199/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree073.table
  base := (-6495192483419936760892011190547573901593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-386090693762057491356110008040000000000000)
      constant := (9177861809019842472039704577347333965377698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree073.table
  base := (-6495194109735982030930290338088910552741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1758361692493886424548676936570000000000000)
      constant := (42313041516119037394795368353080398635177317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80901945072744004959/20000000000000000000)
  centralHi := (101127431340930006199/25000000000000000000)
  directionLo := (6364205219187426289/1562500000000000000)
  directionHi := (407309134027995282497/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree074.table
  base := (-6364294290594235464331969529164872354567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-391257327599910900151058969780000000000000)
      constant := (9429556247728606416033135189191691787036062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree074.table
  base := (-3182147809549307207646760429888836187421/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1781898579977440842392333317830000000000000)
      constant := (43473277574769861538267638960614006640384954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6364205219187426289/1562500000000000000)
  centralHi := (407309134027995282497/100000000000000000000)
  directionLo := (82017886686121985091/20000000000000000000)
  directionHi := (25630589589413120341/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree075.table
  base := (-1557031547635760949197411807930891860581/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-396423961437764308946007931520000000000000)
      constant := (9684645872605718702302784919630870055807464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree075.table
  base := (-3114063637795171370374370967268575627923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1805435467460995260235989699090000000000000)
      constant := (44649163291085294401444604824124159470881702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82017886686121985091/20000000000000000000)
  centralHi := (25630589589413120341/6250000000000000000)
  directionLo := (82570201927872714759/20000000000000000000)
  directionHi := (103212752409840893449/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree076.table
  base := (-6086688289350820719645757441875816234821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-401590595275617717740956893260000000000000)
      constant := (9943130682165996905389323784653738572712506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree076.table
  base := (-6086689175411690068203412943623024977211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1828972354944549678079646080350000000000000)
      constant := (45840698659004703031489096002591749426435707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82570201927872714759/20000000000000000000)
  centralHi := (103212752409840893449/25000000000000000000)
  directionLo := (207797117947437555119/50000000000000000000)
  directionHi := (415594235894875110239/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree077.table
  base := (-2969990340076049498482839880204887677457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-406757229113471126535905855000000000000000)
      constant := (10205010675105557566595836469849263145031204) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree077.table
  base := (-5939981403603201345286810044244743982997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1852509242428104095923302461610000000000000)
      constant := (47047883673170533096700468098112581129071189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207797117947437555119/50000000000000000000)
  centralHi := (415594235894875110239/100000000000000000000)
  directionLo := (104579868299857407509/25000000000000000000)
  directionHi := (418319473199429630037/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree078.table
  base := (-2894001722713385444581192689657957177609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-411923862951324535330854816740000000000000)
      constant := (10470285850269682194276541378529577199026948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree078.table
  base := (-289400201800903022120951442495237311171/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-375209225982331702753391768574000000000000)
      constant := (9654143665760806802648451017407200197584908) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104579868299857407509/25000000000000000000)
  centralHi := (418319473199429630037/100000000000000000000)
  directionLo := (105256767717879888563/25000000000000000000)
  directionHi := (421027070871519554253/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree079.table
  base := (-1407689164714806575473276092910192139959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-417090496789177944125803778480000000000000)
      constant := (10738956206626789329752237289672029240162296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree079.table
  base := (-1407689285229106755728630212780468189591/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1899583017395212931610615224130000000000000)
      constant := (49509202621604815722325646525459322016223068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105256767717879888563/25000000000000000000)
  centralHi := (421027070871519554253/100000000000000000000)
  directionLo := (105929341767122877777/25000000000000000000)
  directionHi := (423717367068491511109/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree080.table
  base := (-5468240386845399868214906906272985507477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-422257130627031352920752740220000000000000)
      constant := (11011021743247335888160125220912178202895322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree080.table
  base := (-1093648156051046395434658137408304890041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-384623980975753469890854321078000000000000)
      constant := (10152667309533918315571088424223276791927417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105929341767122877777/25000000000000000000)
  centralHi := (423717367068491511109/100000000000000000000)
  directionLo := (426390689279512762083/100000000000000000000)
  directionHi := (106597672319878190521/25000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree081.table
  base := (-5300454689715517272208610919210902487781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-427423764464884761715701701960000000000000)
      constant := (11286482459286698709923073721146047365171066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree081.table
  base := (-132511375268318288622427177519891693917/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-389331358472464353459585597330000000000000)
      constant := (10406624020685274287346086340637974586265832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426390689279512762083/100000000000000000000)
  centralHi := (106597672319878190521/25000000000000000000)
  directionLo := (429047354790891613171/100000000000000000000)
  directionHi := (107261838697722903293/25000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree082.table
  base := (-5127399622727219552272247991118673645281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-432590398302738170510650663700000000000000)
      constant := (11565338353971270820503510348244338568966066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree082.table
  base := (-5127399884635514954470890129063622427917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1970193679845876185141584367910000000000000)
      constant := (53318553285581100177562361529368991787041229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429047354790891613171/100000000000000000000)
  centralHi := (107261838697722903293/25000000000000000000)
  directionLo := (53960958890702934053/12500000000000000000)
  directionHi := (17267506845024938897/4000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree083.table
  base := (-2474537618436587055643510173791481347277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-437757032140591579305599625440000000000000)
      constant := (11847589426587154876261098271048838522276244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree083.table
  base := (-4949075450526331381933860800820922731281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-1993730567329430602985240749170000000000000)
      constant := (54619636091074324602260764454828281867929297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53960958890702934053/12500000000000000000)
  centralHi := (17267506845024938897/4000000000000000000)
  directionLo := (86862387291777256213/20000000000000000000)
  directionHi := (217155968229443140533/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree084.table
  base := (-4765481579538759093363771577014617170587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-442923665978444988100548587180000000000000)
      constant := (12133235676470955583178285679321795359611782) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree084.table
  base := (-476548175380360199263217114054880802461/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-403453490962597004165779426086000000000000)
      constant := (11187273703409188835481766328405085018889914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86862387291777256213/20000000000000000000)
  centralHi := (217155968229443140533/50000000000000000000)
  directionLo := (43692044001107444123/10000000000000000000)
  directionHi := (436920440011074441231/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree085.table
  base := (-4576618695038536134720343432415766782173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-448090299816298396895497548920000000000000)
      constant := (12422277103002269078348022788521179265049578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree085.table
  base := (-4576618837157452568537092206049102598427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2040804342296539438672553511690000000000000)
      constant := (57268750560806480978742373014318906536299099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43692044001107444123/10000000000000000000)
  centralHi := (436920440011074441231/100000000000000000000)
  directionLo := (87902692483967548709/20000000000000000000)
  directionHi := (219756731209918871773/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree086.table
  base := (-4382486625054685059987823082798302662759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-453256933654151805690446510660000000000000)
      constant := (12714713705597544844225474378280823762721374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree086.table
  base := (-438248674094225321988490649457787632469/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-412868245956018771303241978590000000000000)
      constant := (11723356443962721937863300554876318758308906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87902692483967548709/20000000000000000000)
  centralHi := (219756731209918871773/50000000000000000000)
  directionLo := (442091276092479967247/100000000000000000000)
  directionHi := (27630704755779997953/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree087.table
  base := (-26144283806225655758212211223085697731/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-91684713498401042897079094480000000000000)
      constant := (2602109096741011658816114408571057607416512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree087.table
  base := (-4183085503481752149110126317563274100041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2087878117263648274359866274210000000000000)
      constant := (59980463491652934172377846646593513731697417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442091276092479967247/100000000000000000000)
  centralHi := (27630704755779997953/6250000000000000000)
  directionLo := (111163536384992430229/25000000000000000000)
  directionHi := (444654145539969720917/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree088.table
  base := (-795683016858656205541070436331679034411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-92718040265971724656068886828000000000000)
      constant := (2661954487360156526717444629939356493518246) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree088.table
  base := (-497301895164969269139607711389530548421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2111415004747202692203522655470000000000000)
      constant := (61359794374022194725721445699939676603595816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111163536384992430229/25000000000000000000)
  centralHi := (444654145539969720917/100000000000000000000)
  directionLo := (89440465538744553081/20000000000000000000)
  directionHi := (223601163846861382703/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree089.table
  base := (-3768475686641109804087569812212455563949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-468756835167712032075293395880000000000000)
      constant := (13612394564384989312796469976804025622104714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree089.table
  base := (-3768475749426771875939769878957944968151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2134951892230757110047179036730000000000000)
      constant := (62754774864718249052773116526805649467006487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89440465538744553081/20000000000000000000)
  centralHi := (223601163846861382703/50000000000000000000)
  directionLo := (224868036103114833313/50000000000000000000)
  directionHi := (449736072206229666627/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree090.table
  base := (-888316812549881868723192911112302090593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-473923469005565440870242357620000000000000)
      constant := (13918411865979439224566262214777711082926792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree090.table
  base := (-3553267301371048500031252322540019040239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2158488779714311527890835417990000000000000)
      constant := (64165404961626297833038357836379978800464943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224868036103114833313/50000000000000000000)
  centralHi := (449736072206229666627/100000000000000000000)
  directionLo := (56531952717065551117/12500000000000000000)
  directionHi := (452255621736524408937/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree091.table
  base := (-3332789807759895889734382502743203376929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-479090102843418849665191319360000000000000)
      constant := (14227824341125053303002011916076595152722994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree091.table
  base := (-416598731182589742008251022584138841871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2182025667197865945734491799250000000000000)
      constant := (65591684662710928630144663581657594023697016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56531952717065551117/12500000000000000000)
  centralHi := (452255621736524408937/100000000000000000000)
  directionLo := (90952242444283576757/20000000000000000000)
  directionHi := (227380606110708941893/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree092.table
  base := (-1553521695441785798767343522814611353273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-484256736681272258460140281100000000000000)
      constant := (14540631989379972556418807095481190882108356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree092.table
  base := (-3107043424862554946268985676051428432673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2205562554681420363578148180510000000000000)
      constant := (67033613966008634634071862024608760008741601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90952242444283576757/20000000000000000000)
  centralHi := (227380606110708941893/50000000000000000000)
  directionLo := (457253073133354347519/100000000000000000000)
  directionHi := (89307240846358271/19531250000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree093.table
  base := (-1438014015008925913149790326304759575087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-489423370519125667255089242840000000000000)
      constant := (14856834810317934823624565217678466731897564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree093.table
  base := (-2876028057701710559344013225869847462491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2229099442164974781421804561770000000000000)
      constant := (68491192869621531330011611974950199609863067) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457253073133354347519/100000000000000000000)
  centralHi := (89307240846358271/19531250000000000)
  directionLo := (229865713862844236711/50000000000000000000)
  directionHi := (459731427725688473423/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree094.table
  base := (-2639743754593496332362110375391524010629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-494590004356979076050038204580000000000000)
      constant := (15176432803526909468030623623944518663851194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree094.table
  base := (-1319871888572988697344574724762445603931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2252636329648529199265460943030000000000000)
      constant := (69964421371712047782941835739659931853904694) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229865713862844236711/50000000000000000000)
  centralHi := (459731427725688473423/100000000000000000000)
  directionLo := (462196493266125018323/100000000000000000000)
  directionHi := (115549123316531254581/25000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree095.table
  base := (-2398190593107221179132837369697910836197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-499756638194832484844987166320000000000000)
      constant := (15499425968607942464749234458099229248293242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree095.table
  base := (-1199095305738722369333112718522896622111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2276173217132083617109117324290000000000000)
      constant := (71453299470498412367821737960066115025614014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462196493266125018323/100000000000000000000)
  centralHi := (115549123316531254581/25000000000000000000)
  directionLo := (464648481259011944703/100000000000000000000)
  directionHi := (1815033129918015409/390625000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree096.table
  base := (-2151368573191912323912139870078508659533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-504923272032685893639936128060000000000000)
      constant := (15825814305174173410378192424858900878766538) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree096.table
  base := (-2151368588153851944539092990517783592879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2299710104615638034952773705550000000000000)
      constant := (72957827164250787505395695972637379633648623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464648481259011944703/100000000000000000000)
  centralHi := (1815033129918015409/390625000000000000)
  directionLo := (467087597657130690159/100000000000000000000)
  directionHi := (5838594970714133627/1250000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree097.table
  base := (-1899277721676783538673095083032017073483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-510089905870539302434885089800000000000000)
      constant := (16155597812849993312109874443332551760971238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree097.table
  base := (-379855546772300971300869953513164607067/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-464649398419838490559286017362000000000000)
      constant := (14895600890257587185495864824988670629754779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467087597657130690159/100000000000000000000)
  centralHi := (5838594970714133627/1250000000000000000)
  directionLo := (469514043063583801459/100000000000000000000)
  directionHi := (23475702153179190073/5000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree098.table
  base := (-82095903231964027853429320302276609697/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-103051307941678542245966810308000000000000)
      constant := (3297755298254063585934628029191072509856968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree098.table
  base := (-410479518640315623588623255642774652763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2346783879582746870640086468070000000000000)
      constant := (76013831329974323515825695089958020787503724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469514043063583801459/100000000000000000000)
  centralHi := (23475702153179190073/5000000000000000000)
  directionLo := (921734400242851619/195312500000000000)
  directionHi := (471928012924340028929/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree099.table
  base := (-55171585098007679149671856287943136763/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5600000000000000000000000000000000000000
      center := (9)
      previous := (0)
      next := (5)
      square := (160739719399883829176189920800000000000)
      linear := (-20816926941849844800991320531200000000000)
      constant := (673014013603198248906919399070968796085318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree099.table
  base := (-689644817764406647696811044606861559311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2370320767066301288483742849330000000000000)
      constant := (77565307798717581898884650609659535443526814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (921734400242851619/195312500000000000)
  centralHi := (471928012924340028929/100000000000000000000)
  directionLo := (237164848855979959267/50000000000000000000)
  directionHi := (94865939542391983707/20000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree100.table
  base := (-277848108703287921760960032170627583469/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-525589807384099528819731975020000000000000)
      constant := (17165319358933057316742493325198444855325736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree100.table
  base := (-138924055173778526862206308457630952159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2393857654549855706327399230590000000000000)
      constant := (79132433855966268606473808133537354000111864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237164848855979959267/50000000000000000000)
  centralHi := (94865939542391983707/20000000000000000000)
  directionLo := (476719283100990681301/100000000000000000000)
  directionHi := (238359641550495340651/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree101.table
  base := (-838226510799494693588296178993303240651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-530756441221952937614680936760000000000000)
      constant := (17508683547492622521719075090709093754630886) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree101.table
  base := (-209556629038397753270038956119727813669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2417394542033410124171055611850000000000000)
      constant := (80715209500207874361699712268597828590955412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476719283100990681301/100000000000000000000)
  centralHi := (238359641550495340651/50000000000000000000)
  directionLo := (479096950135487425191/100000000000000000000)
  directionHi := (59887118766935928149/12500000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree102.table
  base := (-279895939439624102132683151373544326461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-535923075059806346409629898500000000000000)
      constant := (17855442905430071456720267448881540758859092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree102.table
  base := (-279895941618677659482062454885315766729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2440931429516964542014711993110000000000000)
      constant := (82313634729967036585933914849584450213392146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479096950135487425191/100000000000000000000)
  centralHi := (59887118766935928149/12500000000000000000)
  directionLo := (96292575077817697617/20000000000000000000)
  directionHi := (240731437694544244043/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree103.table
  base := (-34511070243611758795056840296369137359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-541089708897659755204578860240000000000000)
      constant := (18205597432424853375828074740601806656615792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree103.table
  base := (-55217713099191298333051377873569736993/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-492893663400103791971673674874000000000000)
      constant := (16785541908760785170310425365809965106569441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96292575077817697617/20000000000000000000)
  centralHi := (240731437694544244043/50000000000000000000)
  directionLo := (483817231118045416759/100000000000000000000)
  directionHi := (12095430777951135419/2500000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree104.table
  base := (103067341148631999300853495579833867/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5600000000000000000000000000000000000000
      center := (9)
      previous := (0)
      next := (5)
      square := (160739719399883829176189920800000000000)
      linear := (-21850253709420526559981112879200000000000)
      constant := (742365885126563857485100132784690588370690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree104.table
  base := (6441707378445894493966326953554643783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2488005204484073377702024755630000000000000)
      constant := (85557433940312778196725151725276147885116658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483817231118045416759/100000000000000000000)
  centralHi := (12095430777951135419/2500000000000000000)
  directionLo := (243080092703791459279/50000000000000000000)
  directionHi := (486160185407582918559/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree105.table
  base := (307124038075910401794931157215463212789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-551422976573366572794476783720000000000000)
      constant := (18916091992342288992151928771176016484979046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree105.table
  base := (153562017863432726424978975618597345481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2511542091967627795545681136890000000000000)
      constant := (87202807918120551205033823934827943265530606) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243080092703791459279/50000000000000000000)
  centralHi := (486160185407582918559/100000000000000000000)
  directionLo := (488491902311940708733/100000000000000000000)
  directionHi := (244245951155970354367/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree106.table
  base := (303316639015371926181288341789364909411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-556589610411219981589425745460000000000000)
      constant := (19276432024660988052940415907210102217463508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree106.table
  base := (30331663805968784916167350189620456719/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-507015795890236442677867503630000000000000)
      constant := (17772766295177137156395500544355784355093188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488491902311940708733/100000000000000000000)
  centralHi := (244245951155970354367/50000000000000000000)
  directionLo := (490812541988427440523/100000000000000000000)
  directionHi := (122703135497106860131/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree107.table
  base := (36456444667058457782370331419574539647/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5600000000000000000000000000000000000000
      center := (9)
      previous := (0)
      next := (5)
      square := (160739719399883829176189920800000000000)
      linear := (-22470249769962935615374988288000000000000)
      constant := (785606688993142038751767069519674043555058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree107.table
  base := (911411115121357281165606743164684059451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2558615866934736631232993899410000000000000)
      constant := (90540504612296958817168911022819375095745413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490812541988427440523/100000000000000000000)
  centralHi := (122703135497106860131/25000000000000000000)
  directionLo := (98624452165159340737/20000000000000000000)
  directionHi := (246561130412898351843/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree108.table
  base := (1221457533649442761982419077766726448463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-566922878086926799179323668940000000000000)
      constant := (20007297592559887053883575467128734170278482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree108.table
  base := (1221457532384306149379103667737268913457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2582152754418291049076650280670000000000000)
      constant := (92232827326072414555332197927347447941547791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98624452165159340737/20000000000000000000)
  centralHi := (246561130412898351843/50000000000000000000)
  directionLo := (247710605783618144277/50000000000000000000)
  directionHi := (99084242313447257711/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree109.table
  base := (1536772509037557357301053802141495302359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-572089511924780207974272630680000000000000)
      constant := (20377823127576226481945978021004980934233026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree109.table
  base := (1536772508008406994047050824615497381673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2605689641901845466920306661930000000000000)
      constant := (93940799615958364632005605857330776335045399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247710605783618144277/50000000000000000000)
  centralHi := (99084242313447257711/20000000000000000000)
  directionLo := (15553423232132638313/3125000000000000000)
  directionHi := (497709543428244426017/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree110.table
  base := (928678011682366120621700329892283749323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-577256145762633616769221592420000000000000)
      constant := (20751743829604904231131579734436983944981044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree110.table
  base := (464339005631904680718475874359309751407/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2629226529385399884763963043190000000000000)
      constant := (95664421480728448458374515495638546057354564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15553423232132638313/3125000000000000000)
  centralHi := (497709543428244426017/100000000000000000000)
  directionLo := (99997480441930085523/20000000000000000000)
  directionHi := (15624606319051575863/3125000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree111.table
  base := (54580201439411578037283026288552744093/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-116484555920097405112834110832000000000000)
      constant := (4225811939675831448269585333407317907338416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree111.table
  base := (2183208056895608126186125078269852497491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2652763416868954302607619424450000000000000)
      constant := (97403692919182747042229494035971000707341933) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99997480441930085523/20000000000000000000)
  centralHi := (15624606319051575863/3125000000000000000)
  directionLo := (100450986081204394377/20000000000000000000)
  directionHi := (251127465203010985943/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree112.table
  base := (1257164296513080084048743525811382723849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-587589413438340434359119515900000000000000)
      constant := (21509770733637933254975756227842718716267772) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree112.table
  base := (15714553702952750593104581823296200097/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-535260060870501744090255161142000000000000)
      constant := (19831722786029388894339612316475765139395552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100450986081204394377/20000000000000000000)
  centralHi := (251127465203010985943/50000000000000000000)
  directionLo := (25225613365484356409/5000000000000000000)
  directionHi := (504512267309687128181/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree113.table
  base := (2850717611462237030303448749183390601159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-592756047276193843154068477640000000000000)
      constant := (21893876935125710063104450118103567468416226) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree113.table
  base := (2850717611011947472096913734371901243511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2699837191836063138294932186970000000000000)
      constant := (100929184512471532215894962865245429778341193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25225613365484356409/5000000000000000000)
  centralHi := (504512267309687128181/100000000000000000000)
  directionLo := (5067595491105860003/1000000000000000000)
  directionHi := (506759549110586000301/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree114.table
  base := (3192375095015866469044449161612644242517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-597922681114047251949017439380000000000000)
      constant := (22281378302592324084387101740062577019395238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree114.table
  base := (319237509464971562330261701619374497473/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-544674815863923511227717713646000000000000)
      constant := (20543080933006210430569540547040041186681598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5067595491105860003/1000000000000000000)
  centralHi := (506759549110586000301/100000000000000000000)
  directionLo := (101799381798430907619/20000000000000000000)
  directionHi := (31812306812009658631/6250000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree115.table
  base := (3539301026189337930066783175952046264083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-603089314951900660743966401120000000000000)
      constant := (22672274835792807371064159222138328647697162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree115.table
  base := (884825256472906654373779857856873792923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2746910966803171973982244949490000000000000)
      constant := (104517274386723374852902101611379932195816596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101799381798430907619/20000000000000000000)
  centralHi := (31812306812009658631/6250000000000000000)
  directionLo := (511224477223431540843/100000000000000000000)
  directionHi := (127806119305857885211/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree116.table
  base := (972873846961240543351994848186192094251/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-608255948789754069538915362860000000000000)
      constant := (23066566534487232273776147964738426757278056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree116.table
  base := (3891495387602915942884388406360499147969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2770447854286726391825901330750000000000000)
      constant := (106334793676469010151815387441640711446322047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511224477223431540843/100000000000000000000)
  centralHi := (127806119305857885211/25000000000000000000)
  directionLo := (256721190623784550913/50000000000000000000)
  directionHi := (513442381247569101827/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree117.table
  base := (4248958163194476107190460605186722485889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-613422582627607478333864324600000000000000)
      constant := (23464253398440563109236781886967614114802446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree117.table
  base := (2124479081498850638479677760244048359121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2793984741770280809669557712010000000000000)
      constant := (108167962533210447463269362915490750093249246) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256721190623784550913/50000000000000000000)
  centralHi := (513442381247569101827/100000000000000000000)
  directionLo := (257825372883458332187/50000000000000000000)
  directionHi := (825041193227066663/160000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree118.table
  base := (4611689335788907579532353203219977660313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-618589216465460887128813286340000000000000)
      constant := (23865335427422514267319714758285079687244382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree118.table
  base := (2305844667814474131611512628065428822591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2817521629253835227513214093270000000000000)
      constant := (110016780955911523622804717315316244031646466) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257825372883458332187/50000000000000000000)
  centralHi := (825041193227066663/160000000000000000)
  directionLo := (517849692824839425197/100000000000000000000)
  directionHi := (258924846412419712599/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree119.table
  base := (4979688889508865330424770460145469409201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-623755850303314295923762248080000000000000)
      constant := (24269812621207414270384822164517036571728814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree119.table
  base := (4979688889378842737387022903350301067997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2841058516737389645356870474530000000000000)
      constant := (111881248943556816338071283034391068967283811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517849692824839425197/100000000000000000000)
  centralHi := (258924846412419712599/50000000000000000000)
  directionLo := (260019670942211492451/50000000000000000000)
  directionHi := (520039341884422984903/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree120.table
  base := (5352956808555223812810488108973699768909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-628922484141167704718711209820000000000000)
      constant := (24677684979574075360773302965925631796764726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree120.table
  base := (2676478404224771285726989705898556175501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2864595404220944063200526855790000000000000)
      constant := (113761366495151061555005225822543218078113126) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260019670942211492451/50000000000000000000)
  centralHi := (520039341884422984903/100000000000000000000)
  directionLo := (5222198099042078653/1000000000000000000)
  directionHi := (522219809904207865301/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree121.table
  base := (1432873269360044083593697972519635776661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-634089117979021113513660171560000000000000)
      constant := (25088952502305668244792751162876099603493016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree121.table
  base := (22388644833415177376456484156077597733/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2888132291704498481044183237050000000000000)
      constant := (115657133609718593245112330485009219496237824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5222198099042078653/1000000000000000000)
  centralHi := (522219809904207865301/100000000000000000000)
  directionLo := (65548901426386218679/12500000000000000000)
  directionHi := (524391211411089749433/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree122.table
  base := (6115297680978633090817136277605503342259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-639255751816874522308609133300000000000000)
      constant := (25503615189189601665182959118006477046791626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree122.table
  base := (1528824420227207789640400034293829908889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2911669179188052898887839618310000000000000)
      constant := (117568550286302804282748926966942045137040028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65548901426386218679/12500000000000000000)
  centralHi := (524391211411089749433/100000000000000000000)
  directionLo := (16454801830328563023/3125000000000000000)
  directionHi := (526553658570514016737/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree123.table
  base := (162609265106998581813439164201116974807/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-128884477130945586220711619008000000000000)
      constant := (5184334608003481302121905493093525101178384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree123.table
  base := (3252185302111610157974608687203575455339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2935206066671607316731495999570000000000000)
      constant := (119495616523965627219032543363467650507372714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16454801830328563023/3125000000000000000)
  centralHi := (526553658570514016737/100000000000000000000)
  directionLo := (132176815313521577293/25000000000000000000)
  directionHi := (528707261254086309173/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree124.table
  base := (6898711832739922622848626708489261736051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-649589019492581339898507056780000000000000)
      constant := (26343126054584624201478831820518849664304714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree124.table
  base := (689871183269383100080704496105318810817/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-591748590831032346915030476166000000000000)
      constant := (24287666464357406775108054734565270170162942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132176815313521577293/25000000000000000000)
  centralHi := (528707261254086309173/100000000000000000000)
  directionLo := (530852127104714443583/100000000000000000000)
  directionHi := (8294564486011163181/1562500000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree125.table
  base := (912290169004146210302281419054921258327/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-654755653330434748693456018520000000000000)
      constant := (26767974232690699117360223268309151180932624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree125.table
  base := (7298321351995719210548921210289984362093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-2982279841638716152418808762090000000000000)
      constant := (123396697678864552780109189708748269014811859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530852127104714443583/100000000000000000000)
  centralHi := (8294564486011163181/1562500000000000000)
  directionLo := (133247090399847738151/25000000000000000000)
  directionHi := (106597672319878190521/20000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree126.table
  base := (1925799787026413883196172553909395736899/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-659922287168288157488404980260000000000000)
      constant := (27196217574138874853395237304858926161266344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree126.table
  base := (120362486688675439176008945973242979669/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3005816729122270570262465143350000000000000)
      constant := (125370712594312803551950944235704115694025408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133247090399847738151/25000000000000000000)
  centralHi := (106597672319878190521/20000000000000000000)
  directionLo := (133779017027429966183/25000000000000000000)
  directionHi := (535116068109719864733/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree127.table
  base := (8113345207167573201045818426805350653471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-665088921006141566283353942000000000000000)
      constant := (27627856078736094111963244181970274909148594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree127.table
  base := (405667260357142666600231869648566166327/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-605870723321164997621224304922000000000000)
      constant := (25472075413452609483290345495031438673914404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133779017027429966183/25000000000000000000)
  centralHi := (535116068109719864733/100000000000000000000)
  directionLo := (537235347960285999459/100000000000000000000)
  directionHi := (26861767398014299973/5000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree128.table
  base := (2132189878921608512118570332029359168957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-670255554843994975078302903740000000000000)
      constant := (28062889746292902052122060934433644113461592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree128.table
  base := (4264379757833176171595590967972119427401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3052890504089379405949777905870000000000000)
      constant := (129365691096862753093492129596044487047852526) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (537235347960285999459/100000000000000000000)
  centralHi := (26861767398014299973/5000000000000000000)
  directionLo := (26967315024248001653/5000000000000000000)
  directionHi := (539346300484960033061/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree129.table
  base := (8949442060380399470544982054229725102011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-675422188681848383873251865480000000000000)
      constant := (28501318576623352933408336206134216151428154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree129.table
  base := (8949442060364086656288929989444166939781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3076427391572933823793434287130000000000000)
      constant := (131386654682275177358546428198914982517206203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26967315024248001653/5000000000000000000)
  centralHi := (539346300484960033061/100000000000000000000)
  directionLo := (67681127885153482997/12500000000000000000)
  directionHi := (541449023081227863977/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree130.table
  base := (2343848207052959277826467553587578346129/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-680588822519701792668200827220000000000000)
      constant := (28943142569544919902838741291600904387383224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree130.table
  base := (4687696414099293317722028144601883937133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3099964279056488241637090668390000000000000)
      constant := (133423267822678959624555832292119837376078758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67681127885153482997/12500000000000000000)
  centralHi := (541449023081227863977/100000000000000000000)
  directionLo := (135885902815657088579/25000000000000000000)
  directionHi := (543543611262628354317/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree131.table
  base := (9806611806381091562829699363940584256029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-685755456357555201463149788960000000000000)
      constant := (29388361724878407784702294740610168179584406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree131.table
  base := (9806611806370329172572257946462043543957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3123501166540042659480747049650000000000000)
      constant := (135475530517267729935711030793667108743269291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135885902815657088579/25000000000000000000)
  centralHi := (543543611262628354317/100000000000000000000)
  directionLo := (545630158709379328031/100000000000000000000)
  directionHi := (17050942459668104001/3125000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree132.table
  base := (5121549491160230099172069149964011594681/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-690922090195408610258098750700000000000000)
      constant := (29836976042447868742224183916318992324651068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree132.table
  base := (10243098982311719199570257019851439727251/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3147038054023597077324403430910000000000000)
      constant := (137543442765249729802721517193250640702816813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545630158709379328031/100000000000000000000)
  centralHi := (17050942459668104001/3125000000000000000)
  directionLo := (273854378658633875041/50000000000000000000)
  directionHi := (547708757317267750083/100000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree133.table
  base := (10684854343688365389971469742622988766057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-696088724033262019053047712440000000000000)
      constant := (30288985522080520688614120776811721842724798) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree133.table
  base := (1068485434368126652651940137165033768929/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-634114988301430299033611962434000000000000)
      constant := (27925400913169489068724483281238794254885054) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273854378658633875041/50000000000000000000)
  centralHi := (547708757317267750083/100000000000000000000)
  directionLo := (5497794972448762791/1000000000000000000)
  directionHi := (549779497244876279101/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree134.table
  base := (2782969469590928725160832695191613855393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-701255357871115427847996674180000000000000)
      constant := (30744390163606668332553148241330730375902008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree134.table
  base := (5565938939178974996229312770533631055031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3194111828990705913011716193430000000000000)
      constant := (141726215918297252225273181308467237512933906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5497794972448762791/1000000000000000000)
  centralHi := (549779497244876279101/100000000000000000000)
  directionLo := (551842466959214864261/100000000000000000000)
  directionHi := (275921233479607432131/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree135.table
  base := (1448021196805055340546355384928715596671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-706421991708968836642945635920000000000000)
      constant := (31203189966859626749957422013187016146827152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree135.table
  base := (5792084787217880681659610488615177739937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3217648716474260330855372574690000000000000)
      constant := (143841076821849071928927483261365512395232062) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551842466959214864261/100000000000000000000)
  centralHi := (275921233479607432131/50000000000000000000)
  directionLo := (138474438319955683019/25000000000000000000)
  directionHi := (553897753279822732077/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree136.table
  base := (6020864710111111543804176671888999831411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-711588625546822245437894597660000000000000)
      constant := (31665384931675647379997302946252891995279508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree136.table
  base := (3010432355054605455089560799896760827827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3241185603957814748699028955950000000000000)
      constant := (145971587275766038889004516762613983728612404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138474438319955683019/25000000000000000000)
  centralHi := (553897753279822732077/100000000000000000000)
  directionLo := (277972720710701484089/50000000000000000000)
  directionHi := (555945441421402968179/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree137.table
  base := (1250455740421735072351341007632465692117/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-143351051876935130846568711880000000000000)
      constant := (6426195011578769269787399343912709039379276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree137.table
  base := (3126139351053566064302216641653682925007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3264722491441369166542685337210000000000000)
      constant := (148117747279324178077803171796796728097101764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277972720710701484089/50000000000000000000)
  centralHi := (555945441421402968179/100000000000000000000)
  directionLo := (111597123007009786289/20000000000000000000)
  directionHi := (278992807517524465723/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree138.table
  base := (2594530703026756179178822520861908100201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-144384378644505812605558504228000000000000)
      constant := (6519992069071227006093963344740066713402814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree138.table
  base := (810790844695704684304894473740431291843/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3288259378924923584386341718470000000000000)
      constant := (150279556831812092630648903255510354742177744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111597123007009786289/20000000000000000000)
  centralHi := (278992807517524465723/50000000000000000000)
  directionLo := (17500573632753716633/3125000000000000000)
  directionHi := (560018356248118932257/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree139.table
  base := (1680752217734290373130965325525501454247/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-727088527060382471822741482880000000000000)
      constant := (33072340793907152755919924622133856162875664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree139.table
  base := (2689203548374457695066504548499882593901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-662359253281695600445999619946000000000000)
      constant := (30491403186506132225215913128491492603415763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17500573632753716633/3125000000000000000)
  centralHi := (560018356248118932257/100000000000000000000)
  directionLo := (281021872851406476657/50000000000000000000)
  directionHi := (112408749140562590663/20000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree140.table
  base := (6962325036765990878631745365182213512171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-732255160898235880617690444620000000000000)
      constant := (33548116403394201592015369924025101978340788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree140.table
  base := (1392465007353033007876316692067682453171/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-667066630778406484014730896198000000000000)
      constant := (30930024916158548830870646794040527989099546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281021872851406476657/50000000000000000000)
  centralHi := (112408749140562590663/20000000000000000000)
  directionLo := (70507732824187835133/12500000000000000000)
  directionHi := (112812372518700536213/20000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree141.table
  base := (14408550499385440726622765100632684648213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-737421794736089289412639406360000000000000)
      constant := (34027287173667183107953291503023857585074982) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree141.table
  base := (3602137624846024977454214824399492311813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3358870041375586837917310862250000000000000)
      constant := (156858882775922899824960644995288672062576876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70507732824187835133/12500000000000000000)
  centralHi := (112812372518700536213/20000000000000000000)
  directionLo := (56607278470286373953/10000000000000000000)
  directionHi := (566072784702863739531/100000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree142.table
  base := (14897719008894682284486719473505610480823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-742588428573942698207588368100000000000000)
      constant := (34509853104578537057212745791749078546731522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree142.table
  base := (14897719008893593876132888795643506027343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3382406928859141255760967243510000000000000)
      constant := (159083290517257107880083073919825540879722609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56607278470286373953/10000000000000000000)
  centralHi := (566072784702863739531/100000000000000000000)
  directionLo := (113615317687371353687/20000000000000000000)
  directionHi := (142019147109214192109/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree143.table
  base := (15392155591696739520943935315609515305267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-747755062411796107002537329840000000000000)
      constant := (34995814195983181903054972930733533214273738) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree143.table
  base := (15392155591695856048343226292803069178343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3405943816342695673604623624770000000000000)
      constant := (161323347804142502096170334909126593358235609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113615317687371353687/20000000000000000000)
  centralHi := (142019147109214192109/25000000000000000000)
  directionLo := (71259168607325232007/12500000000000000000)
  directionHi := (570073348858601856057/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree144.table
  base := (7945930118800787447671414215125128627589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-752921696249649515797486291580000000000000)
      constant := (35485170447738457119910850741223503601572492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree144.table
  base := (317837204752017156115667245564849410287/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25200000000000000000000000000000000000000
      center := (41)
      previous := (0)
      next := (22)
      square := (723328737299477231292854643600000000000)
      linear := (-137179228153050003657931200241200000000000)
      constant := (6543162185437484426804822554560371025696162) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71259168607325232007/12500000000000000000)
  centralHi := (570073348858601856057/100000000000000000000)
  directionLo := (286031569860594408781/50000000000000000000)
  directionHi := (572063139721188817563/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree145.table
  base := (16396832936588081131481313639303650732483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-758088330087502924592435253320000000000000)
      constant := (35977921859704067205913550030725251110254762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree145.table
  base := (2049604117073437389740475680347765765111/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3453017591309804509291936387290000000000000)
      constant := (165850411012009604300010402831995273945615944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286031569860594408781/50000000000000000000)
  centralHi := (572063139721188817563/100000000000000000000)
  directionLo := (35877877093716493423/6250000000000000000)
  directionHi := (574046033499463894769/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree146.table
  base := (4226768419700049979598485546278291445287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-763254963925356333387384215060000000000000)
      constant := (36474068431742027344709554516631584320936072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree146.table
  base := (1690707367879972755908648591510846865971/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-695310895758671785427118553710000000000000)
      constant := (33627483386347810336604426682238366705112346) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35877877093716493423/6250000000000000000)
  centralHi := (574046033499463894769/100000000000000000000)
  directionLo := (72002762677603954677/12500000000000000000)
  directionHi := (576022101420831637417/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree147.table
  base := (871129122727157709558910433753310365917/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-153684319552641948436466635360000000000000)
      constant := (7394722032743322131478045824689185380491352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree147.table
  base := (871129122727138542220439368030870429469/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-700018273255382668995849829962000000000000)
      constant := (34088014478902936433041882154503779348226188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72002762677603954677/12500000000000000000)
  centralHi := (576022101420831637417/100000000000000000000)
  directionLo := (577991413495109003313/100000000000000000000)
  directionHi := (288995706747554501657/50000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree148.table
  base := (17943359254279789948922070854795000233499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-773588231601063150977282138540000000000000)
      constant := (37476547055494296987942805259607130003268986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree148.table
  base := (4485839813569869713778402221428716858987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3523628253760467762822905531070000000000000)
      constant := (172758377399735655289089277559680036648464724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (577991413495109003313/100000000000000000000)
  centralHi := (288995706747554501657/50000000000000000000)
  directionLo := (579954038543467079689/100000000000000000000)
  directionHi := (57995403854346707969/10000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree149.table
  base := (18469404068627023739443681771919473570499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-778754865438916559772231100280000000000000)
      constant := (37982879106943723168036737067781872629986986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree149.table
  base := (9234702034313385645869425855578250562533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3547165141244022180666561912330000000000000)
      constant := (175092331946810836995795621549582859570879158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (579954038543467079689/100000000000000000000)
  centralHi := (57995403854346707969/10000000000000000000)
  directionLo := (290955022113247137907/50000000000000000000)
  directionHi := (116382008845298855163/20000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree150.table
  base := (59377240276101225324961051858004624599/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-156784299855353993713436012404000000000000)
      constant := (7698521263587126941849889496064772143640704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree150.table
  base := (9500358444176093627871027451497897548103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3570702028727576598510218293590000000000000)
      constant := (177441936035158582248720267703388735091060978) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290955022113247137907/50000000000000000000)
  centralHi := (116382008845298855163/20000000000000000000)
  directionLo := (583859497071413362699/100000000000000000000)
  directionHi := (5838594970714133627/1000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree151.table
  base := (4884324426092674857488041973582880411041/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-789088133114623377362129023760000000000000)
      constant := (39005728688342838873004515953235641303018296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree151.table
  base := (19537297704370533213467713881566891074851/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3594238916211131016353874674850000000000000)
      constant := (179807189664206523855242919232578714137715613) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583859497071413362699/100000000000000000000)
  centralHi := (5838594970714133627/1000000000000000000)
  directionLo := (117160492499696666997/20000000000000000000)
  directionHi := (292901231249241667493/50000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree152.table
  base := (20079146507740760806730053359490339732163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-794254766952476786157077985500000000000000)
      constant := (39522246218040159070553437174152864756250282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree152.table
  base := (10039573253870312971182449296802004719369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3617775803694685434197531056110000000000000)
      constant := (182188092833391367272342867543797052594640494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117160492499696666997/20000000000000000000)
  centralHi := (292901231249241667493/50000000000000000000)
  directionLo := (293869502423307869459/50000000000000000000)
  directionHi := (587739004846615738919/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree153.table
  base := (20626263289662236619388324208764110606911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-799421400790330194952026947240000000000000)
      constant := (40042158906904390547287150980137697548496754) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree153.table
  base := (5156565822415531799522916331592166542479/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3641312691178239852041187437370000000000000)
      constant := (184584645542158691190626570183141225968704708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293869502423307869459/50000000000000000000)
  centralHi := (587739004846615738919/100000000000000000000)
  directionLo := (589669187398233844697/100000000000000000000)
  directionHi := (294834593699116922349/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree154.table
  base := (21178648041472555747690197073296749501623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-804588034628183603746975908980000000000000)
      constant := (40565466754814257307522342404026154493022722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree154.table
  base := (1058932402073623348659148182165723407571/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-732969915732358853976968763726000000000000)
      constant := (37399369557992550739924745794621762298707892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589669187398233844697/100000000000000000000)
  centralHi := (294834593699116922349/50000000000000000000)
  directionLo := (59159307240340183773/10000000000000000000)
  directionHi := (591593072403401837731/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree155.table
  base := (5434075188660981091069110231271074790079/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-809754668466037012541924870720000000000000)
      constant := (41092169761650370237675982211426180188244424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree155.table
  base := (21736300754643852343683604601496821263011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3688386466145348687728500199890000000000000)
      constant := (189424699576266303845125167010294299739569693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59159307240340183773/10000000000000000000)
  centralHi := (591593072403401837731/100000000000000000000)
  directionLo := (118702144220650011647/20000000000000000000)
  directionHi := (148377680275812514559/25000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree156.table
  base := (22299221420780417446125028048782166269643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-814921302303890421336873832460000000000000)
      constant := (41622267927295186387425762014322950327775002) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree156.table
  base := (22299221420780359019963286669000863866961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3711923353628903105572156581150000000000000)
      constant := (191868200900540398396884175298187054423618543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118702144220650011647/20000000000000000000)
  centralHi := (148377680275812514559/25000000000000000000)
  directionLo := (23816887750108849149/4000000000000000000)
  directionHi := (297711096876360614363/50000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree157.table
  base := (5716852507903787557002534155144696391133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-820087936141743830131822794200000000000000)
      constant := (42155761251632969370058520307183102997903448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree157.table
  base := (11433705015807551416070332857706373874883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3735460241112457523415812962410000000000000)
      constant := (194327351762264223652198229156571003108235258) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23816887750108849149/4000000000000000000)
  centralHi := (297711096876360614363/50000000000000000000)
  directionLo := (59732754964266157143/10000000000000000000)
  directionHi := (597327549642661571431/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree158.table
  base := (23440866579007526935955985755353597694337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-825254569979597238926771755940000000000000)
      constant := (42692649734549750844738596157614950367720718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree158.table
  base := (23440866579007488489498244876588022486817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3758997128596011941259469343670000000000000)
      constant := (196802152160924922107752126283005045416669471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59732754964266157143/10000000000000000000)
  centralHi := (597327549642661571431/100000000000000000000)
  directionLo := (149806711780319932409/25000000000000000000)
  directionHi := (599226847121279729637/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree159.table
  base := (24019591054940564242905590731459800695627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-830421203817450647721720717680000000000000)
      constant := (43232933375933293044887191779515437209738778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree159.table
  base := (960783642197621322289388785832219352973/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25200000000000000000000000000000000000000
      center := (41)
      previous := (0)
      next := (22)
      square := (723328737299477231292854643600000000000)
      linear := (-151301360643182654364125028997200000000000)
      constant := (7971704083840696953546135379742629819237299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149806711780319932409/25000000000000000000)
  centralHi := (599226847121279729637/100000000000000000000)
  directionLo := (30056007180749773287/5000000000000000000)
  directionHi := (601120143614995465741/100000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree160.table
  base := (12301791725759143494151261110990876270607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-835587837655304056516669679420000000000000)
      constant := (43776612175673052318256517162307744535576996) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree160.table
  base := (24603583451518261693168270941203215082121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3806070903563120776946782106190000000000000)
      constant := (201798701567044282429844549186095802550173623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30056007180749773287/5000000000000000000)
  centralHi := (601120143614995465741/100000000000000000000)
  directionLo := (120601499129739842383/20000000000000000000)
  directionHi := (150751873912174802979/25000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree161.table
  base := (6298210940240798449564430091828689482461/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-840754471493157465311618641160000000000000)
      constant := (44323686133660143645612125467957406611017816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree161.table
  base := (25192843760963173281806651249550628242039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3829607791046675194790438487450000000000000)
      constant := (204320450573515515311049608767261689579248457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120601499129739842383/20000000000000000000)
  centralHi := (150751873912174802979/25000000000000000000)
  directionLo := (60488895886544269439/10000000000000000000)
  directionHi := (604888958865442694391/100000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree162.table
  base := (12893685987806895166849716054708598242701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-845921105331010874106567602900000000000000)
      constant := (44874155249787306106207012153651840750795628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree162.table
  base := (25787371975613773693786446834025661149179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3853144678530229612634094868710000000000000)
      constant := (206857849114948448352118668171643616652398277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60488895886544269439/10000000000000000000)
  centralHi := (604888958865442694391/100000000000000000000)
  directionLo := (606764588045580037193/100000000000000000000)
  directionHi := (303382294022790018597/50000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree163.table
  base := (13193584043961093990298196112316856592321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-851087739168864282901516564640000000000000)
      constant := (45428019523948869259444739506259871984584988) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree163.table
  base := (5277433617584434897052519328856054013687/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-775336313202756806095550249994000000000000)
      constant := (41882179438173512916217897710613931402862281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (606764588045580037193/100000000000000000000)
  centralHi := (303382294022790018597/50000000000000000000)
  directionLo := (608634437125377973771/100000000000000000000)
  directionHi := (152158609281344493443/25000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree164.table
  base := (26992232090451765879223872714582343653313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-856254373006717691696465526380000000000000)
      constant := (45985278956040720413289161333804152811146382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree164.table
  base := (5398446418090350986923327292432118664267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-780043690699467689664281526246000000000000)
      constant := (42395918960160871378500021333159223475848821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608634437125377973771/100000000000000000000)
  centralHi := (152158609281344493443/25000000000000000000)
  directionLo := (610498559215113053133/100000000000000000000)
  directionHi := (305249279607556526567/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree165.table
  base := (5520512795174978853738119217894448999663/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28000000000000000000000000000000000000000
      center := (45)
      previous := (0)
      next := (25)
      square := (803698596999419145880949604000000000000)
      linear := (-172284201368914220098282897624000000000000)
      constant := (9309186709192054550217559950285522285995282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree165.table
  base := (27602563975874885393025655148905594353959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3923755340980892866165064012490000000000000)
      constant := (214563941944297184618474679108081052444299417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610498559215113053133/100000000000000000000)
  centralHi := (305249279607556526567/50000000000000000000)
  directionLo := (612357006616673019317/100000000000000000000)
  directionHi := (306178503308336509659/50000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree166.table
  base := (28218163736970717198761839216427426676787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-866587640682424509286363449860000000000000)
      constant := (47109983293606434289537368635269983973475018) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree166.table
  base := (14109081868485355000595230350756849663347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3947292228464447284008720393750000000000000)
      constant := (217163938620891133839877356783735363057581722) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (612357006616673019317/100000000000000000000)
  centralHi := (306178503308336509659/50000000000000000000)
  directionLo := (307104915420339433613/50000000000000000000)
  directionHi := (614209830840678867227/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree167.table
  base := (28839031366622992733558423493197563299857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-871754274520277918081312411600000000000000)
      constant := (47677428198879577641535559484899765886197998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree167.table
  base := (28839031366622986897016407437033911653617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3970829115948001701852376775010000000000000)
      constant := (219779584830137881319396177014733136434177871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307104915420339433613/50000000000000000000)
  centralHi := (614209830840678867227/100000000000000000000)
  directionLo := (1925178383197323227/312500000000000000)
  directionHi := (616057082623143432641/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree168.table
  base := (14732583428908994420577865517764940131067/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-876920908358131326876261373340000000000000)
      constant := (48248268261681510558635427649937418323669876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree168.table
  base := (29465166857817984108444632804007059017721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (1025)
      previous := (0)
      next := (550)
      square := (18083218432486930782321366090000000000000)
      linear := (-3994366003431556119696033156270000000000000)
      constant := (222410880571595561942791431460332444718116423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell236.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1925178383197323227/312500000000000000)
  centralHi := (616057082623143432641/100000000000000000000)
  directionLo := (154474702985420439467/25000000000000000000)
  directionHi := (617898811941681757869/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree169.table
  base := (3762071275455304153699036937529237216833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (225)
      previous := (0)
      next := (125)
      square := (4018492984997095729404748020000000000000)
      linear := (-882087542195984735671210335080000000000000)
      constant := (48822503481915447228749512601578274568285296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree169.table
  base := (752414255091060734802106168171572597617/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 126000000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (3616643686497386156464273218000000000000)
      linear := (-803580578183022107507937907506000000000000)
      constant := (45011565168965727911745898809154472589198968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell236.Kernel169
