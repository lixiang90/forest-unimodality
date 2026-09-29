import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell157.Parameters
import ForestUnimodality.BinomialMassData.Q29_54.Batch000_049
import ForestUnimodality.BinomialMassData.Q29_54.Batch050_099
import ForestUnimodality.BinomialMassData.Q29_54.Batch100_149
import ForestUnimodality.BinomialMassData.Q643_1188.Batch000_049
import ForestUnimodality.BinomialMassData.Q643_1188.Batch050_099
import ForestUnimodality.BinomialMassData.Q643_1188.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree000.table
  base := (202895338074074466866392187/5000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-274121816625237311182416987000000000000000)
      constant := (21912696512000042421570356196000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree000.table
  base := (202895338074074466866392187/5000000000000000000000000)
  polynomial :=
    { denominator := 11880000000000000000000000000000000000000000
      center := (57227)
      previous := (0)
      next := (48505)
      square := (1390115570243856626397871472400000000000000)
      linear := (-6030679965755220846013173714000000000000000)
      constant := (482079323264000933274547836312000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree001.table
  base := (236460898231653396519320533775382590637009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-9233714118748309318540634680800000000000000)
      constant := (349226796027873446429738883675657817148759122) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree001.table
  base := (235144484722953850702725326224456664711083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-2238034105662700496652828271434600000000000000)
      constant := (84057818584132958292275644372027316749999681388) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49829588068185814597/100000000000000000000)
  directionHi := (24914794034092907299/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree002.table
  base := (14572869690058155233898558111673304878187/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-11066139188615211235156010712600000000000000)
      constant := (222390133023407198504229066369796785123966460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree002.table
  base := (144332111141616334667080695287512391025859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-2684956261496100402039743949811200000000000000)
      constant := (53348217847472291259516253526593421999999986124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49829588068185814597/100000000000000000000)
  centralHi := (24914794034092907299/50000000000000000000)
  directionLo := (70469679253492932331/100000000000000000000)
  directionHi := (17617419813373233083/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree003.table
  base := (95511330037055435580658793981545600556433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-1433173806498012572419042971600000000000000)
      constant := (17289797644748480860539572515160387290142146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree003.table
  base := (94367893934150707398270599506851161107287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-347986490814388923047406625354200000000000000)
      constant := (4143690216555823257906239968344517920050079548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70469679253492932331/100000000000000000000)
  centralHi := (17617419813373233083/25000000000000000000)
  directionLo := (86307378254325732397/100000000000000000000)
  directionHi := (43153689127162866199/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree004.table
  base := (66419108526661238739803994326285490414933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-14730989328349015068386762776200000000000000)
      constant := (120610766637045502810006394888124245024972314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree004.table
  base := (327765209286954364124620828679033868313/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-3578800573162900212813575306564400000000000000)
      constant := (28942358181649559803757149539971918792017133600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86307378254325732397/100000000000000000000)
  centralHi := (43153689127162866199/50000000000000000000)
  directionLo := (19931835227274325839/20000000000000000000)
  directionHi := (24914794034092907299/25000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree005.table
  base := (48540176040891341515474479371341013746329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-16563414398215916985002138808000000000000000)
      constant := (102946409999370613300899500472165198042147682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree005.table
  base := (47892540446693962900699903996658572963709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-4025722728996300118200490984941000000000000000)
      constant := (24769055621767011717320277043428149250223228724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19931835227274325839/20000000000000000000)
  centralHi := (24914794034092907299/25000000000000000000)
  directionLo := (111422346211275907199/100000000000000000000)
  directionHi := (34819483191023721/31250000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree006.table
  base := (36780832209888145213868532781925528673513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-2043982163120313211290834982200000000000000)
      constant := (10576499305606586702441396330271935645109106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree006.table
  base := (36286834769575820455682311550320018007361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-496960542758855558176378518146400000000000000)
      constant := (2552666411688531664737915100113445985960580644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111422346211275907199/100000000000000000000)
  centralHi := (34819483191023721/31250000000000000)
  directionLo := (122057064860132191423/100000000000000000000)
  directionHi := (1907141638439565491/1562500000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree007.table
  base := (227945094460617279164773927485363819129/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-20228264537949720818232890871600000000000000)
      constant := (93476321040694897541595829327557556036260250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree007.table
  base := (1124114261889369925073568572194062330803/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-4919567040663099928974322341694200000000000000)
      constant := (22628143152719427490937205934846929413780182700) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122057064860132191423/100000000000000000000)
  centralHi := (1907141638439565491/1562500000000000000)
  directionLo := (102997420282196171/78125000000000000)
  directionHi := (131836697961211098881/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree008.table
  base := (2227862123622970211133672484325251394591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-22060689607816622734848266903400000000000000)
      constant := (95770924654589044490657258971062165333136780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree008.table
  base := (21958376770206461126861980887503375674443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-5366489196496499834361238020070800000000000000)
      constant := (23243791809552128108993358885870341059467770348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102997420282196171/78125000000000000)
  centralHi := (131836697961211098881/100000000000000000000)
  directionLo := (140939358506985864663/100000000000000000000)
  directionHi := (17617419813373233083/12500000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree009.table
  base := (8690495609977191161285860052447664442693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-884930173247537950054208997600000000000000)
      constant := (3739615834736743526740719015114347759810844) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree009.table
  base := (4277381352795415444689504091873168115839/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-215311531567774064435116803646200000000000000)
      constant := (909573316694024230653716130707169243751136208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140939358506985864663/100000000000000000000)
  centralHi := (17617419813373233083/12500000000000000000)
  directionLo := (9343047762784840237/6250000000000000000)
  directionHi := (149488764204557443793/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree010.table
  base := (209017414322256375620080942111655764171/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-25725539747550426568079018967000000000000000)
      constant := (108455502881583126285761367950322822666324352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree010.table
  base := (13141450817161910131229111945303493118911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-6260333508163299645135069376824000000000000000)
      constant := (26425831778441824706251881064530603298104081596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9343047762784840237/6250000000000000000)
  centralHi := (149488764204557443793/100000000000000000000)
  directionLo := (157574993163416830983/100000000000000000000)
  directionHi := (19696874145427103873/12500000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree011.table
  base := (10019214602181506256719406901867802942833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-27557964817417328484694394998800000000000000)
      constant := (117867292513585235639256798167073256690650514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree011.table
  base := (9811486153791749437899836934415715676191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1545129)
      previous := (0)
      next := (1309635)
      square := (37533120396584128912742529754800000000000000)
      linear := (-609750514908790868229271368654600000000000000)
      constant := (2614566081590454328021261275497493496029502516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157574993163416830983/100000000000000000000)
  centralHi := (19696874145427103873/12500000000000000000)
  directionLo := (165266047080142711101/100000000000000000000)
  directionHi := (82633023540071355551/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree012.table
  base := (7153834722508349285073518881463427104477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-3265598876364914489034419003400000000000000)
      constant := (14331250720710593279167291055197075190925274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree012.table
  base := (3484584280436158339656831022207999030083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-794908646647788828434322303730800000000000000)
      constant := (3500952910461894100140372273134084787950747864) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165266047080142711101/100000000000000000000)
  centralHi := (82633023540071355551/50000000000000000000)
  directionLo := (86307378254325732397/50000000000000000000)
  directionHi := (34522951301730292959/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree013.table
  base := (2339934322392606626469508064123568946861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-31222814957151132317925147062400000000000000)
      constant := (141649981912562280500411038785334327049046676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree013.table
  base := (564384963681669479389450242953834003227/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-7601099975663499361295816411953800000000000000)
      constant := (34635801302914480052142338743247196794900814176) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86307378254325732397/50000000000000000000)
  centralHi := (34522951301730292959/20000000000000000000)
  directionLo := (179663134815092546103/100000000000000000000)
  directionHi := (22457891851886568263/12500000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree014.table
  base := (505307607135592874871974567387430927957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-33055240027018034234540523094200000000000000)
      constant := (155770273982084891543049170408654371464806530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree014.table
  base := (2379366235859748163559030236077537187857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-8048022131496899266682732090330400000000000000)
      constant := (38117255442341622864507926214540953911214712452) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179663134815092546103/100000000000000000000)
  centralHi := (22457891851886568263/12500000000000000000)
  directionLo := (186445246275230105241/100000000000000000000)
  directionHi := (93222623137615052621/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree015.table
  base := (320802770469980650581448140309583482893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-3876407232987215127906211014000000000000000)
      constant := (19029552292496841061642611041210305048457332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree015.table
  base := (510290367523281383915225763831201454643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-943882698592255463563294196523000000000000000)
      constant := (4659409295968510843341879312623363421827824172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186445246275230105241/100000000000000000000)
  centralHi := (93222623137615052621/50000000000000000000)
  directionLo := (48247291184114867579/25000000000000000000)
  directionHi := (192989164736459470317/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree016.table
  base := (-507559480842028488525457924931444568741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-36720090166751838067771275157800000000000000)
      constant := (188078474665474143982452280305299907637551244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree016.table
  base := (-1132064818333906597451638781054515122333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-8941866443163699077456563447083600000000000000)
      constant := (46074001839674154479179210776428649102296513612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48247291184114867579/25000000000000000000)
  centralHi := (192989164736459470317/100000000000000000000)
  directionLo := (19931835227274325839/10000000000000000000)
  directionHi := (199318352272743258391/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree017.table
  base := (-2475502200608924187445189929345934416817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-38552515236618739984386651189600000000000000)
      constant := (206161324391063787251850945957363627620280814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree017.table
  base := (-515881394011861155564689936562995172781/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-9388788598997098982843479125460200000000000000)
      constant := (50524022370401958551133865474011620176083215420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19931835227274325839/10000000000000000000)
  centralHi := (199318352272743258391/100000000000000000000)
  directionLo := (8218106195445903459/4000000000000000000)
  directionHi := (51363163721536896619/25000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree018.table
  base := (-941333878503254040029450099621177934669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-1495738529869838588926001008200000000000000)
      constant := (8350996890302830644544325755281825566111496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree018.table
  base := (-1928710934500701075941665634046251687829/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-364285583512240699564088696438400000000000000)
      constant := (2047247495835264274130402335238667165886901256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8218106195445903459/4000000000000000000)
  centralHi := (51363163721536896619/25000000000000000000)
  directionLo := (42281807552095759399/20000000000000000000)
  directionHi := (52852259440119699249/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree019.table
  base := (-306610958854216795149835250586699983143/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-42217365376352543817617403253200000000000000)
      constant := (245994403517625748398744705386463462793240096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree019.table
  base := (-2493591449356503564091410496205261090589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-10282632910663898793617310482213400000000000000)
      constant := (60321546442765445264192513239068765995681879192) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42281807552095759399/20000000000000000000)
  centralHi := (52852259440119699249/25000000000000000000)
  directionLo := (217202138787482099563/100000000000000000000)
  directionHi := (54300534696870524891/25000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree020.table
  base := (-1182865016701421559188735030293612974123/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-44049790446219445734232779285000000000000000)
      constant := (267688266872306774046214695719159561418643330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree020.table
  base := (-598611818602796898117369473161046317903/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-10729555066497298699004226160590000000000000000)
      constant := (65655465265482340449384349243957490613763770920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217202138787482099563/100000000000000000000)
  centralHi := (54300534696870524891/25000000000000000000)
  directionLo := (222844692422551814399/100000000000000000000)
  directionHi := (34819483191023721/15625000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree021.table
  base := (-6805543451457602926809729454979079395013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-5098023946231816405649795035200000000000000)
      constant := (32281919944470208682995722084643389138007894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree021.table
  base := (-1717178213847362670970207113706459588787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-1241830802481188733821237982107400000000000000)
      constant := (7919147553592754789594018436518332833124777808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222844692422551814399/100000000000000000000)
  centralHi := (34819483191023721/15625000000000000)
  directionLo := (228347859170929842437/100000000000000000000)
  directionHi := (114173929585464921219/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree022.table
  base := (-7591579968111900396120725684646765079419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-47714640585953249567463531348600000000000000)
      constant := (314523727397460545023104574715385016514207098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree022.table
  base := (-3823521369150760151994940310191946812393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1545129)
      previous := (0)
      next := (1309635)
      square := (37533120396584128912742529754800000000000000)
      linear := (-1056672670742190773616187047031200000000000000)
      constant := (7015261255021657624940729664126266228091364264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228347859170929842437/100000000000000000000)
  centralHi := (114173929585464921219/50000000000000000000)
  directionLo := (46744297036105653367/20000000000000000000)
  directionHi := (58430371295132066709/25000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree023.table
  base := (-2070648566252362767968504835607120863203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-49547065655820151484078907380400000000000000)
      constant := (339632797821208255309103779258089271125800104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree023.table
  base := (-1666238769904790362431934212292684761327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-12070321533997498415164973195719800000000000000)
      constant := (83338544025088883144678555019469816397762133140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46744297036105653367/20000000000000000000)
  centralHi := (58430371295132066709/25000000000000000000)
  directionLo := (119487154625546444503/50000000000000000000)
  directionHi := (238974309251092889007/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree024.table
  base := (-8887092571229299714736891559351373549209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-5708832302854117044521587045800000000000000)
      constant := (40650232076608640193767357388985077485028142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree024.table
  base := (-223239994974584724884233687404251144551/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-1390804854425655368950209874899600000000000000)
      constant := (9975706995632740403346130834071349525160903840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119487154625546444503/50000000000000000000)
  centralHi := (238974309251092889007/100000000000000000000)
  directionLo := (244114129720264382847/100000000000000000000)
  directionHi := (1907141638439565491/781250000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree025.table
  base := (-4706101104360525594514326014528160018183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-53211915795553955317309659444000000000000000)
      constant := (393171208366866540435334332910385885386978372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree025.table
  base := (-9449317353351088849962123983354038537633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-12964165845664298225938804552473000000000000000)
      constant := (96493840730730355697096139491237419458535722812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244114129720264382847/100000000000000000000)
  centralHi := (1907141638439565491/781250000000000000)
  directionLo := (249147940340929072987/100000000000000000000)
  directionHi := (62286985085232268247/25000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree026.table
  base := (-246597447322513840827240988324870422261/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-55044340865420857233925035475800000000000000)
      constant := (421581445718298284797687914543293556973738480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree026.table
  base := (-9896253676120295231474041859488527921959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-13411088001497698131325720230849600000000000000)
      constant := (103473893075257657156609526292259805762127674276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249147940340929072987/100000000000000000000)
  centralHi := (62286985085232268247/25000000000000000000)
  directionLo := (50816408382793933407/20000000000000000000)
  directionHi := (63520510478492416759/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree027.table
  base := (-2561797386717629908074241462983606443379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-2106546886492139227797793018800000000000000)
      constant := (16706499862069971847462486386045541008230136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree027.table
  base := (-5137677428585781817239796958127746105087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-513259635456707334693060589230600000000000000)
      constant := (4100732401322498975191542673002348227797446168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50816408382793933407/20000000000000000000)
  centralHi := (63520510478492416759/25000000000000000000)
  directionLo := (32365266845372149649/12500000000000000000)
  directionHi := (258922134762977197193/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree028.table
  base := (-5283139410825530452098236447419773868303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-58709191005154661067155787539400000000000000)
      constant := (481647234032452082802550149046923939400028452) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree028.table
  base := (-2647690727822705296328686908891001825009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-14304932313164497942099551587602800000000000000)
      constant := (118230024560150793834234639705201337920284497904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32365266845372149649/12500000000000000000)
  centralHi := (258922134762977197193/100000000000000000000)
  directionLo := (263673395922422197761/100000000000000000000)
  directionHi := (131836697961211098881/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree029.table
  base := (-10824689870534855788816662762678909648927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-60541616075021562983771163571200000000000000)
      constant := (513291520772486088541115408351164149731864434) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree029.table
  base := (-10845946818398439391737150501209492141921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-14751854468997897847486467265979400000000000000)
      constant := (126003418267588437467487311587081172630613162044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263673395922422197761/100000000000000000000)
  centralHi := (131836697961211098881/50000000000000000000)
  directionLo := (268340544018803645577/100000000000000000000)
  directionHi := (134170272009401822789/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree030.table
  base := (-5512689392037278873714242360205293068517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-6930449016098718322265171067000000000000000)
      constant := (60667116279551720927849985145293485045800492) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree030.table
  base := (-11043812050028777692238627374122355334901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-1688752958314588639208153660484000000000000000)
      constant := (14893214533674011775898885144452407181450541196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268340544018803645577/100000000000000000000)
  centralHi := (134170272009401822789/50000000000000000000)
  directionLo := (13646394708067822031/5000000000000000000)
  directionHi := (272927894161356440621/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree031.table
  base := (-2792706313949328286209727568652679681989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-64206466214755366817001915634800000000000000)
      constant := (579781195869727702831264958459767572094640152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree031.table
  base := (-11186792191744505266634658127549789999989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-15645698780664697658260298622732600000000000000)
      constant := (142335703509988209438313229187615767295563881196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13646394708067822031/5000000000000000000)
  centralHi := (272927894161356440621/100000000000000000000)
  directionLo := (1083747674455254121/390625000000000000)
  directionHi := (277439404660545054977/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree032.table
  base := (-11263109408967366165588513924071746509027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-66038891284622268733617291666600000000000000)
      constant := (614619936014053463961900527188303393589838634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree032.table
  base := (-11276925627678589618154303486191576097831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-16092620936498097563647214301109200000000000000)
      constant := (150893017173050808111187771379853309055945701284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1083747674455254121/390625000000000000)
  centralHi := (277439404660545054977/100000000000000000000)
  directionLo := (281878717013971729327/100000000000000000000)
  directionHi := (17617419813373233083/6250000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree033.table
  base := (-11303976209611533383512612302981974938331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-7541257372721018961136963077600000000000000)
      constant := (72279746976497297019767186760066920059990378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree033.table
  base := (-11315919742671189926962730474828323823751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (171681)
      previous := (0)
      next := (145515)
      square := (4170346710731569879193614417200000000000000)
      linear := (-167066091841732297667011413934200000000000000)
      constant := (1613235044095115551487079151559886853892151436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (281878717013971729327/100000000000000000000)
  centralHi := (17617419813373233083/6250000000000000000)
  directionLo := (286249190308877278013/100000000000000000000)
  directionHi := (143124595154438639007/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree034.table
  base := (-90359115867439357683858484427738235729/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-69703741424356072566848043730200000000000000)
      constant := (687472421935123577517769348119444706538389750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree034.table
  base := (-2826301171002039219197633744771308628293/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-16986465248164897374421045657862400000000000000)
      constant := (168786955479637353484567654531441782195310444208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286249190308877278013/100000000000000000000)
  centralHi := (143124595154438639007/50000000000000000000)
  directionLo := (72638482741387212757/25000000000000000000)
  directionHi := (290553930965548851029/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree035.table
  base := (-2809269305133367212301023042895660754161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-71536166494222974483463419762000000000000000)
      constant := (725482243044415421062948476087582506481733048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree035.table
  base := (-5622989192856578540258323045347198402193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-17433387403998297279807961336239000000000000000)
      constant := (178122652841464375340206477135881876809127661304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72638482741387212757/25000000000000000000)
  centralHi := (290553930965548851029/100000000000000000000)
  directionLo := (294795818570375949593/100000000000000000000)
  directionHi := (147397909285187974797/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree036.table
  base := (-11131569576242161013115212182509581939627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-2717355243114439866669585029400000000000000)
      constant := (28316506820366469357861131367344482575260142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree036.table
  base := (-2784811069508174292659771789060431211131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-662233687401173969822032482022800000000000000)
      constant := (6952481755725298101850119676008633139731760368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294795818570375949593/100000000000000000000)
  centralHi := (147397909285187974797/50000000000000000000)
  directionLo := (59795505681822977517/20000000000000000000)
  directionHi := (149488764204557443793/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree037.table
  base := (-10979230747043337265459329860889427169249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-75201016633956778316694171825600000000000000)
      constant := (804661485253082789045466305389173215187234958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree037.table
  base := (-5492921435913736076129570368932082533499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-18327231715665097090581792692992200000000000000)
      constant := (197569722606503329530988000746401284454420693672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59795505681822977517/20000000000000000000)
  centralHi := (149488764204557443793/50000000000000000000)
  directionLo := (303101551201355922367/100000000000000000000)
  directionHi := (4735961737521186287/1562500000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree038.table
  base := (-2156157141938521024642194475029432420021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-77033441703823680233309547857400000000000000)
      constant := (845828589337870094452846890888635437658046910) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree038.table
  base := (-10786478213428319896152064068017751066437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-18774153871498496995968708371368800000000000000)
      constant := (207680550034334030172337926957515588784722634668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303101551201355922367/100000000000000000000)
  centralHi := (4735961737521186287/1562500000000000000)
  directionLo := (153585105224850231803/50000000000000000000)
  directionHi := (307170210449700463607/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree039.table
  base := (-526842132583843558593223847667442237251/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-8762874085965620238880547098800000000000000)
      constant := (98671789962988964342526839970907487151306760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree039.table
  base := (-10541740043367490865710385494739854029721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-2135675114147988544595069338860600000000000000)
      constant := (24227697956264968172166827083707543762618817916) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153585105224850231803/50000000000000000000)
  centralHi := (307170210449700463607/100000000000000000000)
  directionLo := (311185677746837118137/100000000000000000000)
  directionHi := (155592838873418559069/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree040.table
  base := (-2561977946880886035088235586887224161163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-80698291843557484066540299921000000000000000)
      constant := (931313302347393581008365853957273708692097384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree040.table
  base := (-5126061178410657835869832317293521169367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-19667998183165296806742539728122000000000000000)
      constant := (228675743023373343875084360701090846329370450376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311185677746837118137/100000000000000000000)
  centralHi := (155592838873418559069/50000000000000000000)
  directionLo := (157574993163416830983/50000000000000000000)
  directionHi := (315149986326833661967/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree041.table
  base := (-4957210571698900623009704892516484413189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-82530716913424385983155675952800000000000000)
      constant := (975629543317199971846833619436571931451140876) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree041.table
  base := (-2479509737540851616924327927871907836117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-20114920338998696712129455406498600000000000000)
      constant := (239559788283042641331309379006914475106943288752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157574993163416830983/50000000000000000000)
  centralHi := (315149986326833661967/100000000000000000000)
  directionLo := (79766260775173817453/25000000000000000000)
  directionHi := (319065043100695269813/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree042.table
  base := (-4768364899256996207582610446524351673147/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-9373682442587920877752339109400000000000000)
      constant := (113443812115425036600621944453726110057900372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree042.table
  base := (-4769918221536260124198430757503925201707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-2284649166092455179724041231652800000000000000)
      constant := (27855699453943514668350496701091932232784557544) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79766260775173817453/25000000000000000000)
  centralHi := (319065043100695269813/100000000000000000000)
  directionLo := (161466319689195257493/50000000000000000000)
  directionHi := (322932639378390514987/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree043.table
  base := (-364605559725624715189380673194398962483/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-86195567053158189816386428016400000000000000)
      constant := (1067407160303958180346482938089414157817494650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree043.table
  base := (-1139725648266766700982712533532329235953/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-21008764650665496522903286763251800000000000000)
      constant := (262100160984581138707090799108412021653626298336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161466319689195257493/50000000000000000000)
  centralHi := (322932639378390514987/100000000000000000000)
  directionLo := (163377230224210483767/50000000000000000000)
  directionHi := (65350892089684193507/20000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree044.table
  base := (-1081237680867266037632775283930787663709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-88027992123025091733001804048200000000000000)
      constant := (1114867728647333587605263642436631292690498224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree044.table
  base := (-8652188397295239340219847562203363209819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1545129)
      previous := (0)
      next := (1309635)
      square := (37533120396584128912742529754800000000000000)
      linear := (-1950516982408990584390018403784400000000000000)
      constant := (24886936378569419659782673771115564921681845756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163377230224210483767/50000000000000000000)
  centralHi := (65350892089684193507/20000000000000000000)
  directionLo := (165266047080142711101/50000000000000000000)
  directionHi := (330532094160285422203/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree045.table
  base := (-8141229175978314691450943367687642211281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-3328163599736740505541377040000000000000000)
      constant := (43087989072204402958740826884394867320590826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree045.table
  base := (-814318981477114649437189615727143169497/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-811207739345640604951004374815000000000000000)
      constant := (10580357064383782514190089551266151930610132040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165266047080142711101/50000000000000000000)
  centralHi := (330532094160285422203/100000000000000000000)
  directionLo := (334267038633827721599/100000000000000000000)
  directionHi := (104458449573071163/31250000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree046.table
  base := (-3794650025166300830880188101643616537617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-91692842262758895566232556111800000000000000)
      constant := (1212930829875949920106065639004007214176308828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree046.table
  base := (-7590980107300435811759827158935108182649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-22349531118165696239064033798381600000000000000)
      constant := (297840122488801627709172395468826272169266857436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (334267038633827721599/100000000000000000000)
  centralHi := (104458449573071163/31250000000000000)
  directionLo := (337960709201637758527/100000000000000000000)
  directionHi := (5280636081275589977/1562500000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree047.table
  base := (-6994263295143080667049904905169444736717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-93525267332625797482847932143600000000000000)
      constant := (1263532885856369538923976970595612949573866614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree047.table
  base := (-6995702243526870837914612286861267478431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-22796453273999096144450949476758200000000000000)
      constant := (310267694971097724781378378298511342827980319684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (337960709201637758527/100000000000000000000)
  centralHi := (5280636081275589977/1562500000000000000)
  directionLo := (170807222337873528521/50000000000000000000)
  directionHi := (341614444675747057043/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree048.table
  base := (-317812205269848267389767010443323258387/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-10595299155832522155495923130600000000000000)
      constant := (146131298928498486539102509844563632642826120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree048.table
  base := (-1271495197904465647676511567107480478011/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-2582597269981388449981985017237200000000000000)
      constant := (35883590658607631380509518871724391676700283780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170807222337873528521/50000000000000000000)
  centralHi := (341614444675747057043/100000000000000000000)
  directionLo := (345229513017302929589/100000000000000000000)
  directionHi := (34522951301730292959/10000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree049.table
  base := (-2837673758599927868917519981137549779291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-97190117472359601316078684207200000000000000)
      constant := (1367877090233658475040566167278152904843587444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree049.table
  base := (-2838200838010343901105984577390081301263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-23690297585665895955224780833511400000000000000)
      constant := (335893949957619681429545622243442911547975136264) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345229513017302929589/100000000000000000000)
  centralHi := (34522951301730292959/10000000000000000000)
  directionLo := (174403558238650351091/50000000000000000000)
  directionHi := (348807116477300702183/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree050.table
  base := (-4951661655336735297569735677762609388017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-99022542542226503232694060239000000000000000)
      constant := (1421618957001949321604643440081822115512271214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree050.table
  base := (-4952563353944938198291072030905927140857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-24137219741499295860611696511888000000000000000)
      constant := (349092567405359258166282389458740776291328579548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (174403558238650351091/50000000000000000000)
  centralHi := (348807116477300702183/100000000000000000000)
  directionLo := (352348396267464661659/100000000000000000000)
  directionHi := (17617419813373233083/5000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree051.table
  base := (-4185260457609915577956863898341666860617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-11206107512454822794367715141200000000000000)
      constant := (164045242540004794255873162725818649968580046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree051.table
  base := (-1046507859388695224393867844084626866959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-2731571321925855085110956910029400000000000000)
      constant := (40283127047333519622954431075170350153230957456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352348396267464661659/100000000000000000000)
  centralHi := (17617419813373233083/5000000000000000000)
  directionLo := (44481804601590221317/12500000000000000000)
  directionHi := (355854436812721770537/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree052.table
  base := (-105506436257903534553525690679705725031/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-102687392681960307065924812302600000000000000)
      constant := (1532241677359111488039258733107247649692953664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree052.table
  base := (-422108114801700187409450658579721446429/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-25031064053166095671385527868641200000000000000)
      constant := (376260657205199678029185078767286123229822218848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44481804601590221317/12500000000000000000)
  centralHi := (355854436812721770537/100000000000000000000)
  directionLo := (179663134815092546103/50000000000000000000)
  directionHi := (359326269630185092207/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree053.table
  base := (-2524550215137484461856526488061980921521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-104519817751827208982540188334400000000000000)
      constant := (1589122364607525319718718665986755631816422382) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree053.table
  base := (-631278304966032077737456443299275517423/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-25477986208999495576772443547017800000000000000)
      constant := (390230091304618707548942328021654552294138153488) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179663134815092546103/50000000000000000000)
  centralHi := (359326269630185092207/100000000000000000000)
  directionLo := (72552975374794813007/20000000000000000000)
  directionHi := (90691219218493516259/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree054.table
  base := (-407584224524372091499870024855257162681/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-3938971956359041144413169050600000000000000)
      constant := (61001821515774773234372025619831264452860904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree054.table
  base := (-1630817750386166894883430946954929791793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-960181791290107240079976267607200000000000000)
      constant := (14979867819031717944092116000534092977480849076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72552975374794813007/20000000000000000000)
  centralHi := (90691219218493516259/25000000000000000000)
  directionLo := (366171194580396574271/100000000000000000000)
  directionHi := (5721424915318696473/1562500000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree055.table
  base := (-693602658135337074011093298637944798959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-108184667891561012815770940398000000000000000)
      constant := (1706022072880046643798179210044335876483117778) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree055.table
  base := (-347006602365648086247479958846975077363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1545129)
      previous := (0)
      next := (1309635)
      square := (37533120396584128912742529754800000000000000)
      linear := (-2397439138242390489776934082161000000000000000)
      constant := (38085424035577758250318350824899423854837008824) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (366171194580396574271/100000000000000000000)
  centralHi := (5721424915318696473/1562500000000000000)
  directionLo := (18477305782193986819/5000000000000000000)
  directionHi := (369546115643879736381/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree056.table
  base := (285621750741203285074638274567934991177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-110017092961427914732386316429800000000000000)
      constant := (1766040995630565296112990655270720049217136066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree056.table
  base := (285271346210014955291311761772053782599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-26818752676499695292933190582147600000000000000)
      constant := (433679780879858866852859991511121404368437100764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18477305782193986819/5000000000000000000)
  centralHi := (369546115643879736381/100000000000000000000)
  directionLo := (372890492550460210483/100000000000000000000)
  directionHi := (93222623137615052621/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree057.table
  base := (1307310520030299694239216258080087252897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-12427724225699424072111299162400000000000000)
      constant := (203011767949853240192629561866958974134969314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree057.table
  base := (1307011542503667759266445623315460159131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-3029519425814788355368900695613800000000000000)
      constant := (49852974664922806125482484923640384300078571724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (372890492550460210483/100000000000000000000)
  centralHi := (93222623137615052621/25000000000000000000)
  directionLo := (376205139892545736909/100000000000000000000)
  directionHi := (37620513989254573691/10000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree058.table
  base := (2371441990216377164984333009163114059629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-113681943101161718565617068493400000000000000)
      constant := (1889216789054814532326974882096959820298939082) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree058.table
  base := (296398371311847683182423408557802294179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-27712596988166495103707021938900800000000000000)
      constant := (463930630502022172070184126529079905842151533152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376205139892545736909/100000000000000000000)
  centralHi := (37620513989254573691/10000000000000000000)
  directionLo := (379490836685966626957/100000000000000000000)
  directionHi := (189745418342983313479/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree059.table
  base := (3477997982573858862688406763921324691151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-115514368171028620482232444525200000000000000)
      constant := (1952373601644389516868038864941947291399698158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree059.table
  base := (21736128264307805830692258754307107961/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-28159519143999895009093937617277400000000000000)
      constant := (479441350396728692488197736017946477439124383360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (379490836685966626957/100000000000000000000)
  centralHi := (189745418342983313479/50000000000000000000)
  directionLo := (2990221316468670339/781250000000000000)
  directionHi := (382748328507989803393/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree060.table
  base := (4626963238619502628764665417144287062989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-13038532582321724710983091173000000000000000)
      constant := (224064036341170616476626499067577374504204218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree060.table
  base := (4626777859233394040780433240612053551563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-3178493477759254990497872588406000000000000000)
      constant := (55023214067692400879512271442704954947435475852) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2990221316468670339/781250000000000000)
  centralHi := (382748328507989803393/100000000000000000000)
  directionLo := (48247291184114867579/12500000000000000000)
  directionHi := (385978329472918940633/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree061.table
  base := (5818324949869564148034466816270250027701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-119179218310762424315463196588800000000000000)
      constant := (2081824946658483327380243301837272024540388058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree061.table
  base := (581816696250478325006661812588697171949/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-29053363455666694819867768974030600000000000000)
      constant := (511233354898857686192255013735151380553617973640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48247291184114867579/12500000000000000000)
  centralHi := (385978329472918940633/100000000000000000000)
  directionLo := (389181524060110351279/100000000000000000000)
  directionHi := (4864769050751379391/1250000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree062.table
  base := (1410414472670476767622739061638228802289/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-121011643380629326232078572620600000000000000)
      constant := (2148119444730400174468737255006942687968686810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree062.table
  base := (1762984439167333315572201017747302293497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-29500285611500094725254684652407200000000000000)
      constant := (527514631710631067103428778343442248608113229968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389181524060110351279/100000000000000000000)
  centralHi := (4864769050751379391/1250000000000000000)
  directionLo := (392358568807660091281/100000000000000000000)
  directionHi := (196179284403830045641/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree063.table
  base := (1665639290134229133426522555883975917619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-4549780312981341783284961061200000000000000)
      constant := (82054066967514204880764973072138673497757130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree063.table
  base := (832808179435669083858840934072830297841/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-1109155843234573875208948160399400000000000000)
      constant := (20150102002370940173842438157929612463321861880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (392358568807660091281/100000000000000000000)
  centralHi := (196179284403830045641/50000000000000000000)
  directionLo := (197755046941816648321/50000000000000000000)
  directionHi := (395510093883633296643/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree064.table
  base := (192933792607560547454057022058475188923/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-124676493520363130065309324684200000000000000)
      constant := (2283846025782182474457432114930462841272486700) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree064.table
  base := (9646591992129738476556883895286570273899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-30394129923166894536028516009160400000000000000)
      constant := (560847719459719020172126346335274132309161427564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197755046941816648321/50000000000000000000)
  centralHi := (395510093883633296643/100000000000000000000)
  directionLo := (19931835227274325839/5000000000000000000)
  directionHi := (398636704545486516781/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree065.table
  base := (5503772767535301227738563679830041894541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-126508918590230031981924700716000000000000000)
      constant := (2353278088424624264663022442459134402164481556) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree065.table
  base := (1100746240923556015100488442419420791707/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-30841052079000294441415431687537000000000000000)
      constant := (577899525801630477659906619420673112544627310520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19931835227274325839/5000000000000000000)
  centralHi := (398636704545486516781/100000000000000000000)
  directionLo := (401738982497256042237/100000000000000000000)
  directionHi := (200869491248628021119/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree066.table
  base := (3102689704001302696723494057017708174567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-14260149295566325988726675194200000000000000)
      constant := (269306220916860071769998071010547474897119416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree066.table
  base := (2482137612455002162280427851859570868201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 35640000000000000000000000000000000000000000
      center := (171681)
      previous := (0)
      next := (145515)
      square := (4170346710731569879193614417200000000000000)
      linear := (-316040143786198932795983306726400000000000000)
      constant := (6012203750822496327414522733191837552871341820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (401738982497256042237/100000000000000000000)
  centralHi := (200869491248628021119/50000000000000000000)
  directionLo := (404817487153131371187/100000000000000000000)
  directionHi := (101204371788282842797/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree067.table
  base := (110850599833463268124332028489476263089/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-130173768729963835815155452779600000000000000)
      constant := (2495279718711281158122954163171557048947970250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree067.table
  base := (13856264769958661262391373951307312151291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-31734896390667094252189263044290200000000000000)
      constant := (612773654573799559394946660543640791790212911276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (404817487153131371187/100000000000000000000)
  centralHi := (101204371788282842797/25000000000000000000)
  directionLo := (407872756815187117071/100000000000000000000)
  directionHi := (25492047300949194817/6250000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree068.table
  base := (7672120123918730929573452058262897628761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-132006193799830737731770828811400000000000000)
      constant := (2567849274296720632387383264645494609485467076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree068.table
  base := (383604725576598166779365847180153820543/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-32181818546500494157576178722666800000000000000)
      constant := (630595974290567686660568250179781470137004397920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (407872756815187117071/100000000000000000000)
  centralHi := (25492047300949194817/6250000000000000000)
  directionLo := (410905309772295172951/100000000000000000000)
  directionHi := (51363163721536896619/12500000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree069.table
  base := (16874501447071798395543981883177367451291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-14870957652188626627598467204800000000000000)
      constant := (293496072264339904125750181081424733527109142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree069.table
  base := (8437228937750721748468067893740317573257/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-3625415633592654895884788266782600000000000000)
      constant := (72075014382471681281846137976133715820283934856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410905309772295172951/100000000000000000000)
  centralHi := (51363163721536896619/12500000000000000000)
  directionLo := (82783129065314012461/20000000000000000000)
  directionHi := (206957822663285031153/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree070.table
  base := (18447105907074653515050621541152595874239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-135671043939564541565001580875000000000000000)
      constant := (2716125843065711848555142734297000484784640462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree070.table
  base := (9223534426531603369395276798825398325749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-33075662858167293968350010079420000000000000000)
      constant := (667011119155842238370595260456148216487327948328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82783129065314012461/20000000000000000000)
  centralHi := (206957822663285031153/50000000000000000000)
  directionLo := (41690424475310397967/10000000000000000000)
  directionHi := (416904244753103979671/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree071.table
  base := (5015512845481013930459923336889238017599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-137503469009431443481616956906800000000000000)
      constant := (2791832849082124532216640623172888036118637368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree071.table
  base := (20062019876981533023104801055518439366529/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-33522585014000693873736925757796600000000000000)
      constant := (685603942697894932831689102568206829072328626244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41690424475310397967/10000000000000000000)
  centralHi := (416904244753103979671/100000000000000000000)
  directionLo := (419871572198215288109/100000000000000000000)
  directionHi := (41987157219821528811/10000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree072.table
  base := (4343867196293314535921012281665234048977/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-5160588669603642422156753071800000000000000)
      constant := (106243913543424203102589294452849613193223790) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree072.table
  base := (2714913649986761862201324158013007637159/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-1258129895179040510337920053191600000000000000)
      constant := (26090874053772995583368453168572911870419150496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (419871572198215288109/100000000000000000000)
  centralHi := (41987157219821528811/10000000000000000000)
  directionLo := (422818075520957593991/100000000000000000000)
  directionHi := (52852259440119699249/12500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree073.table
  base := (5854739528541453556514779462023728222649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-141168319149165247314847708970400000000000000)
      constant := (2946384290516238646358338383176872382994488968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree073.table
  base := (5854733838050188165620726491259777335601/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-34416429325667493684510757114549800000000000000)
      constant := (723560088899242247237245197146707864183936457744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (422818075520957593991/100000000000000000000)
  centralHi := (52852259440119699249/12500000000000000000)
  directionLo := (42574418708220936257/10000000000000000000)
  directionHi := (425744187082209362571/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree074.table
  base := (25160916439153078494707991248010555001053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-143000744219032149231463085002200000000000000)
      constant := (3025228721658493452660574857493999389191535274) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree074.table
  base := (12580448548562492080909093449392737956653/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-34863351481500893589897672792926400000000000000)
      constant := (742923410603629751319179601588878172179347235816) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42574418708220936257/10000000000000000000)
  centralHi := (425744187082209362571/100000000000000000000)
  directionLo := (428650324485280626239/100000000000000000000)
  directionHi := (1339532264016501957/312500000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree075.table
  base := (2694520982599773516080782793545658621551/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-16092574365433227905342051226000000000000000)
      constant := (345013217494561115962571537169293966966912620) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree075.table
  base := (26945193393066676238903852293188348025227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-3923363737481588166142732052367000000000000000)
      constant := (84727062688613263941221067518905280995980999308) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (428650324485280626239/100000000000000000000)
  centralHi := (1339532264016501957/312500000000000000)
  directionLo := (215768445635814330993/50000000000000000000)
  directionHi := (431536891271628661987/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree076.table
  base := (7192959330238443986852494211806555902521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-146665594358765953064693837065800000000000000)
      constant := (3186054996503346739298254181015655834023502472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree076.table
  base := (14385911681031259109629668734707109950489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-35757195793167693400671504149679600000000000000)
      constant := (782420549371134057007534190871495035692981473608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215768445635814330993/50000000000000000000)
  centralHi := (431536891271628661987/100000000000000000000)
  directionLo := (434404277574964199127/100000000000000000000)
  directionHi := (54300534696870524891/12500000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree077.table
  base := (47876247060373933876245281494308849853/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-148498019428632854981309213097600000000000000)
      constant := (3268036837641136753898625843458319473974831360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree077.table
  base := (30640786263362451629647738653137339719869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1545129)
      previous := (0)
      next := (1309635)
      square := (37533120396584128912742529754800000000000000)
      linear := (-3291283449909190300550765438914200000000000000)
      constant := (72959487805737318936122757728436608308854518044) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (434404277574964199127/100000000000000000000)
  centralHi := (54300534696870524891/12500000000000000000)
  directionLo := (218626430368374965767/50000000000000000000)
  directionHi := (87450572147349986307/20000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree078.table
  base := (32552091538273917383155942991374537629717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-16703382722055528544213843236600000000000000)
      constant := (372340497763538022400289735681002675096014154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree078.table
  base := (2034505091955727012029481847070759057323/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-4072337789426054801271703945159200000000000000)
      constant := (91438334828076457776100855868673292609332654272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218626430368374965767/50000000000000000000)
  centralHi := (87450572147349986307/20000000000000000000)
  directionLo := (4400830058858404907/1000000000000000000)
  directionHi := (440083005885840490701/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree079.table
  base := (3450571700373955321477068906668273562983/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-152162869568366658814539965161200000000000000)
      constant := (3435137922355483006567893329003373428548292140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree079.table
  base := (34505708456702218225810226933030361048947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-37097962260667893116832251184809400000000000000)
      constant := (843592491953164484202524008132638625471066263692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4400830058858404907/1000000000000000000)
  centralHi := (440083005885840490701/100000000000000000000)
  directionLo := (442895066484784635023/100000000000000000000)
  directionHi := (27680941655299039689/6250000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree080.table
  base := (1825083701342470131098594447280998960223/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-153995294638233560731155341193000000000000000)
      constant := (3520257164380282781511233084762713929680102680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree080.table
  base := (9125416692858064803253438526355752177797/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-37544884416501293022219166863186000000000000000)
      constant := (864496801206411930977706695029901032701620729168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (442895066484784635023/100000000000000000000)
  centralHi := (27680941655299039689/6250000000000000000)
  directionLo := (445689384845103628799/100000000000000000000)
  directionHi := (34819483191023721/7812500000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree081.table
  base := (1204373818540867810318668123195505071703/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-5771397026225943061028545082400000000000000)
      constant := (133571192790451792671819083526331832763902784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree081.table
  base := (38539956035283575411878595212527427346819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-1407103947123507145466891945983800000000000000)
      constant := (32802145965862327976405021491784083420568230692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (445689384845103628799/100000000000000000000)
  centralHi := (34819483191023721/7812500000000000)
  directionLo := (448466292613672331377/100000000000000000000)
  directionHi := (224233146306836165689/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree082.table
  base := (20310290575463875124981789205090644693113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-157660144777967364564386093256600000000000000)
      constant := (3693633044727741361122672775391644319925117508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree082.table
  base := (10155143981277443116129098652354472914409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-38438728728168092832992998219939200000000000000)
      constant := (907075911454759576158550768025113271220913655696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448466292613672331377/100000000000000000000)
  centralHi := (224233146306836165689/50000000000000000000)
  directionLo := (56403263904019921253/12500000000000000000)
  directionHi := (18049044449286374801/4000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree083.table
  base := (8548706119948608128545222208541496591071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-159492569847834266481001469288400000000000000)
      constant := (3781889682099560788777507949023617510148907590) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree083.table
  base := (2137176308283595945060102080601788794711/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-38885650884001492738379913898315800000000000000)
      constant := (928750712238727889740500329117409580023413007920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56403263904019921253/12500000000000000000)
  centralHi := (18049044449286374801/4000000000000000000)
  directionLo := (226984576185664070383/50000000000000000000)
  directionHi := (453969152371328140767/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree084.table
  base := (44908810283708883733031085374743335890201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-17924999435300129821957427257800000000000000)
      constant := (430132457453815936538912111210308420414212562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree084.table
  base := (2806800407623438683783320977007191869759/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-4370285893314988071529647730743600000000000000)
      constant := (105631371483030344641917485126788639200992509376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226984576185664070383/50000000000000000000)
  centralHi := (453969152371328140767/100000000000000000000)
  directionLo := (228347859170929842437/50000000000000000000)
  directionHi := (3653565746734877479/800000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree085.table
  base := (47116419983736265929669657357580106327589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-163157419987568070314232221352000000000000000)
      constant := (3961540349362657499524793436376101795025624762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree085.table
  base := (47116416792844988473133498401311685008909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-39779495195668292549153745255069000000000000000)
      constant := (972870804709413753128006025860688334691803415924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228347859170929842437/50000000000000000000)
  centralHi := (3653565746734877479/800000000000000000)
  directionLo := (229703051241615159513/50000000000000000000)
  directionHi := (459406102483230319027/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree086.table
  base := (6170794938980589083265965855314069093763/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-164989845057434972230847597383800000000000000)
      constant := (4052934378660427468883283697456783301909651632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree086.table
  base := (3085397300346553421307700989967862179097/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-40226417351501692454540660933445600000000000000)
      constant := (995316096264202021272676423711801109917181905472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229703051241615159513/50000000000000000000)
  centralHi := (459406102483230319027/100000000000000000000)
  directionLo := (462100589532060005139/100000000000000000000)
  directionHi := (23105029476603000257/5000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree087.table
  base := (51658628706253602134880893611389142623431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-18535807791922430460829219268400000000000000)
      constant := (460597133860197465592256578735195041104995822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree087.table
  base := (51658626411261578072093293717456923859623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-4519259945259454706658619623535800000000000000)
      constant := (113113135328792367616180684600732106242992660092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462100589532060005139/100000000000000000000)
  centralHi := (23105029476603000257/5000000000000000000)
  directionLo := (232389727985620359961/50000000000000000000)
  directionHi := (464779455971240719923/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree088.table
  base := (53993227427260926899869982397078837472429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-168654695197168776064078349447400000000000000)
      constant := (4238859827403021137024095692316540945034801482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree088.table
  base := (10798645096264453153237455719534918056351/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1545129)
      previous := (0)
      next := (1309635)
      square := (37533120396584128912742529754800000000000000)
      linear := (-3738205605742590205937681117290800000000000000)
      constant := (94634288158981926016181544158178210157877573380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232389727985620359961/50000000000000000000)
  centralHi := (464779455971240719923/100000000000000000000)
  directionLo := (467442970361056533671/100000000000000000000)
  directionHi := (58430371295132066709/12500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree089.table
  base := (2818507777689138357585148175263102995031/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-170487120267035677980693725479200000000000000)
      constant := (4333391246467618953882549569261822083335103960) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree089.table
  base := (11274030780804295093719585782820075216707/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-41567183819001892170701407968575400000000000000)
      constant := (1064192951593797952711158696026720445295810155260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467442970361056533671/100000000000000000000)
  centralHi := (58430371295132066709/12500000000000000000)
  directionLo := (58761424206677231123/12500000000000000000)
  directionHi := (94018278730683569797/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree090.table
  base := (29394706490223576609718664147181922742879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-6382205382848243699900337093000000000000000)
      constant := (164035868954886604041682839327895647656230932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree090.table
  base := (14697352895490127459916878359983520706821/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-1556077999067973780595863838776000000000000000)
      constant := (40283909757768734865576882111545558594386947312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58761424206677231123/12500000000000000000)
  centralHi := (94018278730683569797/20000000000000000000)
  directionLo := (472724979490250492949/100000000000000000000)
  directionHi := (9454499589805009859/2000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree091.table
  base := (2450039984606124797829789422010917985217/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-174151970406769481813924477542800000000000000)
      constant := (4525591473211695995553372248600447960561159650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree091.table
  base := (239261712616467541117972764251270029623/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-42461028130668691981475239325328600000000000000)
      constant := (1111395005316569586780820436077753369716047571968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (472724979490250492949/100000000000000000000)
  centralHi := (9454499589805009859/2000000000000000000)
  directionLo := (475343974487005394407/100000000000000000000)
  directionHi := (59417996810875674301/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree092.table
  base := (31877457688510060783559031941688362358889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-175984395476636383730539853574600000000000000)
      constant := (4623260280638968177443162946517563264638520324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree092.table
  base := (63754914372466073734278622150155779942961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-42907950286502091886862155003705200000000000000)
      constant := (1135381277137733815617421049245731564771954587396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475343974487005394407/100000000000000000000)
  centralHi := (59417996810875674301/12500000000000000000)
  directionLo := (477948618502185778013/100000000000000000000)
  directionHi := (238974309251092889007/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree093.table
  base := (13260232038933005467552785009502500841487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-19757424505167031738572803289600000000000000)
      constant := (524663875995519805574160221726847025681604470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree093.table
  base := (16575289835855589052411943884596746983051/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-4817208049148387976916563409120200000000000000)
      constant := (128847153211087634230817801541387848474894125616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477948618502185778013/100000000000000000000)
  centralHi := (238974309251092889007/50000000000000000000)
  directionLo := (480539144893725601173/100000000000000000000)
  directionHi := (240269572446862800587/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree094.table
  base := (68889734004754028193311086420748689706571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-179649245616370187563770605638200000000000000)
      constant := (4821735283081485520110356138509851589592180518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree094.table
  base := (1722243332087704360289056328838939516919/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-43801794598168891697635986360458400000000000000)
      constant := (1184124310581854712754375191505724942535665291360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480539144893725601173/100000000000000000000)
  centralHi := (240269572446862800587/50000000000000000000)
  directionLo := (483115780762994838459/100000000000000000000)
  directionHi := (24155789038149741923/5000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree095.table
  base := (17880159187696316521197519089291941097301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-181481670686237089480385981670000000000000000)
      constant := (4922541477922010278236507885762500600479459432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree095.table
  base := (17880159034938229671331028036438176822657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-44248716754002291603022902038835000000000000000)
      constant := (1208881072165241891620340978782041927229596021008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483115780762994838459/100000000000000000000)
  centralHi := (24155789038149741923/5000000000000000000)
  directionLo := (485678747187153722299/100000000000000000000)
  directionHi := (4856787471871537223/1000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree096.table
  base := (7419386838206511263933506269151939693067/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-20368232861789332377444595300200000000000000)
      constant := (558265940934149023819806539333626142302768540) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree096.table
  base := (74193867864461817545049675924178355931507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-4966182101092854612045535301912400000000000000)
      constant := (137099407070346868031473813643094688265938800428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485678747187153722299/100000000000000000000)
  centralHi := (4856787471871537223/1000000000000000000)
  directionLo := (244114129720264382847/50000000000000000000)
  directionHi := (97645651888105753139/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree097.table
  base := (38454714426423496327904087078582289561433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-185146520825970893313616733733600000000000000)
      constant := (5127291254470779821892350026923495956361138628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree097.table
  base := (76909428414434603544353903952159738851713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-45142561065669091413796733395588200000000000000)
      constant := (1259165084970251865178432511360357558617483008068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244114129720264382847/50000000000000000000)
  centralHi := (97645651888105753139/20000000000000000000)
  directionLo := (490764527205637950359/100000000000000000000)
  directionHi := (12269113180140948759/2500000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree098.table
  base := (39833659060803327643387637170534377019481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-186978945895837795230232109765400000000000000)
      constant := (5231234836051783743043222433634878243388806596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree098.table
  base := (19916829437577181627536746766902940971803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-45589483221502491319183649073964800000000000000)
      constant := (1284692336162743525552973228594044564322908333232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490764527205637950359/100000000000000000000)
  centralHi := (12269113180140948759/2500000000000000000)
  directionLo := (493287754774450526323/100000000000000000000)
  directionHi := (123321938693612631581/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree099.table
  base := (10308442018803999563135168941228004017381/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-6993013739470544338772129103600000000000000)
      constant := (197637933818336190005899409891060497735508592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree099.table
  base := (41233767918003489309246925832345737411633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11880000000000000000000000000000000000000000
      center := (57227)
      previous := (0)
      next := (48505)
      square := (1390115570243856626397871472400000000000000)
      linear := (-155004731910221855974985066506200000000000000)
      constant := (4412378509083728807094681881677178472090040008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493287754774450526323/100000000000000000000)
  centralHi := (123321938693612631581/25000000000000000000)
  directionLo := (495798141240428133303/100000000000000000000)
  directionHi := (61974767655053516663/12500000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree100.table
  base := (21327520726127265139035010314701874742059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-190643796035571599063462861829000000000000000)
      constant := (5442259385549901235750348007805341333495688088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree100.table
  base := (4265504131913633079555998013584751565247/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-46483327533169291129957480430718000000000000000)
      constant := (1336517328063889495247161107449223788065509809840) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495798141240428133303/100000000000000000000)
  centralHi := (61974767655053516663/12500000000000000000)
  directionLo := (19931835227274325839/4000000000000000000)
  directionHi := (62286985085232268247/12500000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree101.table
  base := (88194958351688804570378313047138968410209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-192476221105438500980078237860800000000000000)
      constant := (5549340353369382755312576777433878615942084722) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree101.table
  base := (88194958126278161953407387280345553379279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-46930249689002691035344396109094600000000000000)
      constant := (1362815068749932552345164703967427928672131285244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19931835227274325839/4000000000000000000)
  centralHi := (62286985085232268247/12500000000000000000)
  directionLo := (500781162336957016187/100000000000000000000)
  directionHi := (125195290584239254047/25000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree102.table
  base := (91122162462121690803971452995465043247613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-21589849575033933655188179321400000000000000)
      constant := (628607457390000118090608215897665337006113306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree102.table
  base := (45561081135647545949320264372158886851497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-5264130204981787882303479087496800000000000000)
      constant := (154374404360651135284551222397636534000252176776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500781162336957016187/100000000000000000000)
  centralHi := (125195290584239254047/25000000000000000000)
  directionLo := (503254170771190710493/100000000000000000000)
  directionHi := (251627085385595355247/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree103.table
  base := (94091695207949251805601172195049177894533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-196141071245172304813308989924400000000000000)
      constant := (5766639674931138512715017439511731701370229114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree103.table
  base := (94091695046416072950081833779433524997831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-47824094000669490846118227465847800000000000000)
      constant := (1416181039542178599102331829779356532226134698716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503254170771190710493/100000000000000000000)
  centralHi := (251627085385595355247/50000000000000000000)
  directionLo := (101143017207446183351/20000000000000000000)
  directionHi := (126428771509307729189/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree104.table
  base := (3034486142595109985236296250178938251901/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-197973496315039206729924365956200000000000000)
      constant := (5876858028594700527597651932378748543080693056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree104.table
  base := (12137944553289980961917699072585149914589/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-48271016156502890751505143144224400000000000000)
      constant := (1443249269629953445788919252920550031642111395232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101143017207446183351/20000000000000000000)
  centralHi := (126428771509307729189/25000000000000000000)
  directionLo := (508164083827939334071/100000000000000000000)
  directionHi := (63520510478492416759/12500000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree105.table
  base := (6259859156424167124842484759976434195473/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-22200657931656234294059971332000000000000000)
      constant := (665346908607199369549295349036608917434666016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree105.table
  base := (100157746387072751972911847354228854529031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-5413104256926254517432450980289000000000000000)
      constant := (163397147722304455476959272134018313012956131324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508164083827939334071/100000000000000000000)
  centralHi := (63520510478492416759/12500000000000000000)
  directionLo := (255300667811373948599/50000000000000000000)
  directionHi := (510601335622747897199/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree106.table
  base := (12906783125485561991288133217050196037683/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-201638346454773010563155118019800000000000000)
      constant := (6100432121507456936035431803250073486583534512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree106.table
  base := (103254264905960708390727815419743925003753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-49164860468169690562278974500977600000000000000)
      constant := (1498156219146524215402767848974403067522624193508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255300667811373948599/50000000000000000000)
  centralHi := (510601335622747897199/100000000000000000000)
  directionLo := (513027008827780067049/100000000000000000000)
  directionHi := (10260540176555601341/2000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree107.table
  base := (106393112044208238580524595935759595776497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-203470771524639912479770494051600000000000000)
      constant := (6213787860690424645118015237077687490642132626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree107.table
  base := (106393111961346847442945540248628779098261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-49611782624003090467665890179354200000000000000)
      constant := (1525994938559671527630358493979540508901914018196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513027008827780067049/100000000000000000000)
  centralHi := (10260540176555601341/2000000000000000000)
  directionLo := (20617650676401488123/4000000000000000000)
  directionHi := (128860316727509300769/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree108.table
  base := (27393571900665099770548537723965053959097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-7603822096092844977643921114200000000000000)
      constant := (234377384999368047926402289083176451655164952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree108.table
  base := (27393571883137663623086316731791653353803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-1854026102956907050853807624360400000000000000)
      constant := (57558906953069822441217307954697813304109990416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20617650676401488123/4000000000000000000)
  centralHi := (128860316727509300769/25000000000000000000)
  directionLo := (32365266845372149649/6250000000000000000)
  directionHi := (103568853905190878877/20000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree109.table
  base := (56398895829530297617475780554353013566759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-207135621664373716313001246115200000000000000)
      constant := (6443636724355571885471843464611643387560669244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree109.table
  base := (112797791599745204403224001575283345757637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-50505626935669890278439721536107400000000000000)
      constant := (1582442866659169597293113409817634599583741608532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32365266845372149649/6250000000000000000)
  centralHi := (103568853905190878877/20000000000000000000)
  directionLo := (130059043161152962067/25000000000000000000)
  directionHi := (520236172644611848269/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree110.table
  base := (29015906048512090648970216244279833891957/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-208968046734240618229616622147000000000000000)
      constant := (6560129848780100862337188743166639991257893224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree110.table
  base := (58031812071934800750628965578568119802301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1545129)
      previous := (0)
      next := (1309635)
      square := (37533120396584128912742529754800000000000000)
      linear := (-4632049917409390016711512474044000000000000000)
      constant := (146459279575618121053177369291418802021557213752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130059043161152962067/25000000000000000000)
  centralHi := (520236172644611848269/100000000000000000000)
  directionLo := (32663570541616931971/6250000000000000000)
  directionHi := (522617128665870911537/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree111.table
  base := (3730368287156256176395175820498025872969/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-23422274644900835571803555353200000000000000)
      constant := (741963196469930128497360790762811766125471296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree111.table
  base := (29842946286638552068435041941113199640337/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-5711052360815187787690394765873400000000000000)
      constant := (182213123749365882151882980493194932514799086992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32663570541616931971/6250000000000000000)
  centralHi := (522617128665870911537/100000000000000000000)
  directionLo := (262493643266843967471/50000000000000000000)
  directionHi := (524987286533687934943/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree112.table
  base := (15340284328244825185777167037211079167563/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-212632896873974422062847374210600000000000000)
      constant := (6796253482677200734500067020099630027410454832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree112.table
  base := (122722274590056636440146999579282351699533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-51846393403170089994600468571237200000000000000)
      constant := (1669040981890390267327753832134078867844256425588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262493643266843967471/50000000000000000000)
  centralHi := (524987286533687934943/100000000000000000000)
  directionLo := (263673395922422197761/50000000000000000000)
  directionHi := (527346791844844395523/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree113.table
  base := (5044603699502849531298167975803533578969/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-214465321943841323979462750242400000000000000)
      constant := (6915883992098289890756637714728388798953420050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree113.table
  base := (63057546228603400488647365194895558017543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-52293315559003489899987384249613800000000000000)
      constant := (1698420679764033091348132042654981663217355603896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263673395922422197761/50000000000000000000)
  centralHi := (527346791844844395523/100000000000000000000)
  directionLo := (66211973369164735607/12500000000000000000)
  directionHi := (529695786953317884857/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree114.table
  base := (1036401910056308995746247686149325484253/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-24033083001523136210675347363800000000000000)
      constant := (781840032940904997578675497698123841056123250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree114.table
  base := (32387559682839902910812679407383750939523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-5860026412759654422819366658665600000000000000)
      constant := (192006356373260936040830990014320990287332238768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66211973369164735607/12500000000000000000)
  centralHi := (529695786953317884857/100000000000000000000)
  directionLo := (53203441107050567887/10000000000000000000)
  directionHi := (532034411070505678871/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree115.table
  base := (66513856709034509064184511650440020936301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-218130172083575127812693502306000000000000000)
      constant := (7158282395763012637141843219166433101050253716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree115.table
  base := (133027713396354106110349475890880357999891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-53187159870670289710761215606367000000000000000)
      constant := (1757950564670634097081950255346512786995249540876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53203441107050567887/10000000000000000000)
  centralHi := (532034411070505678871/100000000000000000000)
  directionLo := (53436280036150055883/10000000000000000000)
  directionHi := (534362800361500558831/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree116.table
  base := (34136879113709847625749099221405977803037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-219962597153442029729308878337800000000000000)
      constant := (7281050289959822891626254272803639662547311784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree116.table
  base := (136547516436478021194439583255530095934647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-53634082026503689616148131284743600000000000000)
      constant := (1788100751692346257398702827203889016929197108892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53436280036150055883/10000000000000000000)
  centralHi := (534362800361500558831/100000000000000000000)
  directionLo := (107336217607521458231/20000000000000000000)
  directionHi := (134170272009401822789/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree117.table
  base := (140109647851961540014868178776719664386069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-8214630452715145616515713124800000000000000)
      constant := (274254221445782953472652469332992861876847726) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree117.table
  base := (70054823918218479944736160957081487606569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-2003000154901373685982779517152600000000000000)
      constant := (67352139571077351535396682233483256760085287384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107336217607521458231/20000000000000000000)
  centralHi := (134170272009401822789/25000000000000000000)
  directionLo := (538989404445277638309/100000000000000000000)
  directionHi := (53898940444527763831/10000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree118.table
  base := (143714107594452558963424691353595146814333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-223627447293175833562539630401400000000000000)
      constant := (7529723462970118114120514406757141724055297514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree118.table
  base := (143714107581327447038646869670895511330787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-54527926338170489426921962641496800000000000000)
      constant := (1849171614845602316692548059746682788635909561932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538989404445277638309/100000000000000000000)
  centralHi := (53898940444527763831/10000000000000000000)
  directionLo := (270643938575815955809/50000000000000000000)
  directionHi := (541287877151631911619/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree119.table
  base := (1178887165341671909877521517058676396489/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-225459872363042735479155006433200000000000000)
      constant := (7655628741740466160043770840916093773260120250) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree119.table
  base := (73680447828306639864903073331822760559481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-54974848494003889332308878319873400000000000000)
      constant := (1880092290966758837418501890101575956089530076232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270643938575815955809/50000000000000000000)
  centralHi := (541287877151631911619/100000000000000000000)
  directionLo := (135894157756681460239/25000000000000000000)
  directionHi := (543576631026725840957/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree120.table
  base := (151050012057484104894753269669501377600941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-25254699714767737488418931385000000000000000)
      constant := (864731090591823573034082571946459223171352442) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree120.table
  base := (75525006024052336720252030586929388544169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-6157974516648587693077310444250000000000000000)
      constant := (212363310753061265202423346905679959496971202952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135894157756681460239/25000000000000000000)
  centralHi := (543576631026725840957/100000000000000000000)
  directionLo := (13646394708067822031/2500000000000000000)
  directionHi := (545855788322712881241/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree121.table
  base := (154781456749867862121615844094809794693319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-229124722502776539312385758496800000000000000)
      constant := (7910576683707675259829958115177382680662859102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree121.table
  base := (154781456741939784548232520319747430102501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 320760000000000000000000000000000000000000000
      center := (1545129)
      previous := (0)
      next := (1309635)
      square := (37533120396584128912742529754800000000000000)
      linear := (-5078972073242789922098428152420600000000000000)
      constant := (176609466570280818858734680948661393567967822076) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13646394708067822031/2500000000000000000)
  centralHi := (545855788322712881241/100000000000000000000)
  directionLo := (137031367187510990143/25000000000000000000)
  directionHi := (548125468750043960573/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree122.table
  base := (79277614865634551654174114239388633614419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-230957147572643441229001134528600000000000000)
      constant := (8039619346864439560551512263995657255619645804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree122.table
  base := (7927761486228412827626368967002274916803/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-56315614961504089048469625355003200000000000000)
      constant := (1974395297448590645705118227973056993450902066160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137031367187510990143/25000000000000000000)
  centralHi := (548125468750043960573/100000000000000000000)
  directionLo := (550385789550839061707/100000000000000000000)
  directionHi := (137596447387709765427/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree123.table
  base := (162371330988399699626292113290007508896101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-25865508071390038127290723395600000000000000)
      constant := (907745311641925663071024642075131216441168362) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree123.table
  base := (162371330982736493312889691981754033495939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-6306948568593054328206282337042200000000000000)
      constant := (222927032477708883972343472062704610129174792556) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550385789550839061707/100000000000000000000)
  centralHi := (137596447387709765427/25000000000000000000)
  directionLo := (276318432784778941259/50000000000000000000)
  directionHi := (552636865569557882519/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree124.table
  base := (1662297605082603407883689587861537076593/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-234621997712377245062231886592200000000000000)
      constant := (8300842057427396486694526148274612105767259400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree124.table
  base := (83114880251737204768066044862900153934731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-57209459273170888859243456711756400000000000000)
      constant := (2038548116820880624569493493850333277427429494232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276318432784778941259/50000000000000000000)
  centralHi := (552636865569557882519/100000000000000000000)
  directionLo := (554878809321090109953/100000000000000000000)
  directionHi := (277439404660545054977/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree125.table
  base := (170130518278127738808400716176954859408559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-236454422782244146978847262624000000000000000)
      constant := (8433022104796085563833577777654750185017679022) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree125.table
  base := (8506525913704172405594476555824277313929/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-57656381429004288764630372390133000000000000000)
      constant := (2071009771008612144063732204063969419206749052880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554878809321090109953/100000000000000000000)
  centralHi := (277439404660545054977/50000000000000000000)
  directionLo := (557111731056379535999/100000000000000000000)
  directionHi := (34819483191023721/6250000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree126.table
  base := (34814720857108609112536530249594954619149/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 540000000000000000000000000000000000000000
      center := (2581)
      previous := (0)
      next := (2225)
      square := (63187071374720755745357794200000000000000)
      linear := (-8825438809337446255387505135400000000000000)
      constant := (317268442476490118462667228308590637747170230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree126.table
  base := (43518401070531421730306369715995512750769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130680000000000000000000000000000000000000000
      center := (629497)
      previous := (0)
      next := (533555)
      square := (15291271272682422890376586196400000000000000)
      linear := (-2151974206845840321111751409944800000000000000)
      constant := (77915861291043924723890751375335417442508197168) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (557111731056379535999/100000000000000000000)
  centralHi := (34819483191023721/6250000000000000)
  directionLo := (22373429553027612629/4000000000000000000)
  directionHi := (279667869412845157863/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree127.table
  base := (89029509259150657778708209307022761016273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-240119272921977950812078014687600000000000000)
      constant := (8700519583617044580139880320734628371123452068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree127.table
  base := (17805901851541388545721344104020026486649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-58550225740671088575404203746886200000000000000)
      constant := (2136703568365301997821945827354654425654432865640) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22373429553027612629/4000000000000000000)
  centralHi := (279667869412845157863/50000000000000000000)
  directionLo := (70193867317452261417/12500000000000000000)
  directionHi := (561550938539618091337/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree128.table
  base := (182086760964441871440267503634042713057773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14580000000000000000000000000000000000000000
      center := (69687)
      previous := (0)
      next := (60075)
      square := (1706050927117460405124660443400000000000000)
      linear := (-241951697991844852728693390719400000000000000)
      constant := (8835837015034081041197469524516034275638233034) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree128.table
  base := (182086760962002344858233507141557757265747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3528360000000000000000000000000000000000000000
      center := (16996419)
      previous := (0)
      next := (14405985)
      square := (412864324362425418040167827302800000000000000)
      linear := (-58997147896504488480791119425262800000000000000)
      constant := (2169935711525745362290880301983321872842617108492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell157.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70193867317452261417/12500000000000000000)
  centralHi := (561550938539618091337/100000000000000000000)
  directionLo := (281878717013971729327/50000000000000000000)
  directionHi := (112751486805588691731/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 29
  qDenominator := 54
  table := BinomialMassData.Q29_54.Degree129.table
  base := (93078415806119725881744299800517330767009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1620000000000000000000000000000000000000000
      center := (7743)
      previous := (0)
      next := (6675)
      square := (189561214124162267236073382600000000000000)
      linear := (-27087124784634639405034307416800000000000000)
      constant := (996911137899916350052663022499717615168510916) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q29_54.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 643
  qDenominator := 1188
  table := BinomialMassData.Q643_1188.Degree129.table
  base := (186156831610178474485060005717799224591117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 392040000000000000000000000000000000000000000
      center := (1888491)
      previous := (0)
      next := (1600665)
      square := (45873813818047268671129758589200000000000000)
      linear := (-6604896672481987598464226122626600000000000000)
      constant := (244824964926153715257896875778692925800870150868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q643_1188.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell157.Kernel129
