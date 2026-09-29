import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell227.Parameters
import ForestUnimodality.BinomialMassData.Q9_14.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_14.Batch050_099
import ForestUnimodality.BinomialMassData.Q41_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q41_63.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel000
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
  base := (661200606524984689892576737/100000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-16152219342432103110773766600000000000000)
      constant := (925680849134978565849607431800000000000000) }

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
  base := (661200606524984689892576737/100000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-72684987040944463998481949700000000000000)
      constant := (4165563821107403546323233443100000000000000) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel001
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
  base := (47820543914082910267533973126403199798437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-186580519100332904020023149880000000000000)
      constant := (4782728106811418728795434925127513580246826) }

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
  base := (47598927734936289294230878237514310909549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-843696501712792967103693440220000000000000)
      constant := (21431223542622582728111497863163811111111109) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel002
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
  base := (34143841588553044996161787226922952884857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-260095502803641086264629933560000000000000)
      constant := (3585985714521483571935313483798449382715986) }

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
  base := (8453821702168839031157474336007634164777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-1178598094138974686218013232540000000000000)
      constant := (16010686135648832420842782539797466666666628) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel003
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
  base := (1494725081154567707511444902815965491063/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-333610486506949268509236717240000000000000)
      constant := (2774452234086337084581003938075433889986784) }

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
  base := (11775139557906355957192756896043023052269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-1513499686565156405332333024860000000000000)
      constant := (12359817814595369615819963334289946332101258) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel004
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
  base := (16255318053757525406179554816680140504261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-407125470210257450753843500920000000000000)
      constant := (2261838176477600283057501915474653769417578) }

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
  base := (15894247194883626862504120880877635819587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-1848401278991338124446652817180000000000000)
      constant := (10077459638956248470804859691587037396437867) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel005
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
  base := (5249363863470356609867628666277259932567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-480640453913565632998450284600000000000000)
      constant := (1983045657203638679992055193090342946783132) }

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
  base := (2541040630017778265930343160961684314253/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-2183302871417519843560972609500000000000000)
      constant := (8862396028846177319575895040436411130342292) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel006
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
  base := (6160302247899931787889427294560026411693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-554155437616873815243057068280000000000000)
      constant := (1890492925392426208034505498506882588345914) }

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
  base := (5862696711099429550024468886048721799449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-2518204463843701562675292401820000000000000)
      constant := (8495305168563554395239424494867486313557009) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel007
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
  base := (359862695669059603138140270112826578887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-89667203045740285355380550280000000000000)
      constant := (278398322288322549600318923232636576835344) }

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
  base := (10240335630039287721093161876780675103/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-407586579467126183112801742020000000000000)
      constant := (1259108034531878995230381145888718728061184) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel008
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
  base := (96533647921155148388745485416965383533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-701185405023490179732270635640000000000000)
      constant := (2131629322494988279188154806443450430344936) }

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
  base := (33618563502224821618338527527389891093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-3188007648696065000903931986460000000000000)
      constant := (9697551464413816919263708263277894709860065) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel009
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
  base := (-758706834546529343758732971309729273809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-774700388726798361976877419320000000000000)
      constant := (2419473455215654169478138217163293062333436) }

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
  base := (-1699246879717608776596152703065607030953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-3522909241122246720018251778780000000000000)
      constant := (11057765709384761435829142550368067299349727) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel010
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
  base := (-1489947723051548714740768845281838087987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-848215372430106544221484203000000000000000)
      constant := (2797801735726246949757989707324759734754548) }

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
  base := (-1564830569297137354062969684087871266561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-3857810833548428439132571571100000000000000)
      constant := (12828615902660609549906917403634497542893198) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel011
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
  base := (-4111373375017359870224455500909924046053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-921730356133414726466090986680000000000000)
      constant := (3255828025730923924714761501450827443486806) }

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
  base := (-169339741000893100223233316728592724547/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-4192712425974610158246891363420000000000000)
      constant := (14961440531677938127281356810887265211869325) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel012
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
  base := (-2496805642382999146919829866932830029869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-995245339836722908710697770360000000000000)
      constant := (3785539469994530170507296444241165314145676) }

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
  base := (-1273091557851808962255202995209603122501/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-4527614018400791877361211155740000000000000)
      constant := (17420244209585935480046010197330260091908236) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel013
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
  base := (-2843674666967644391961268878944450673163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1068760323540031090955304554040000000000000)
      constant := (4380983532975610630943246573586887668060052) }

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
  base := (-576665506945646192718303654090355805481/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-4862515610826973596475530948060000000000000)
      constant := (20178401203421610782967790009641530897828790) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel014
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
  base := (-1559427318794090855971338239125433328011/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-163182186749048467599987333960000000000000)
      constant := (719676897559193480264030011128975733631384) }

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
  base := (-6301019459334273439060448856385055731783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-742488171893307902227121534340000000000000)
      constant := (3316602386984645997255829816007741488897671) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel015
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
  base := (-3339105107824736998884013330246341943793/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1215790290946647455444518121400000000000000)
      constant := (5752518847309056688386274666771716979016572) }

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
  base := (-3364246641351892205059289559547480928403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-5532318795679337034704170532700000000000000)
      constant := (26519122784185235788284767489979121821148554) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel016
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
  base := (-7033751966508742112224852946249293841677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1289305274649955637689124905080000000000000)
      constant := (6522885044666613693105319520707569203515654) }

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
  base := (-353675551320330914309378923840179277971/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-5867220388105518753818490325020000000000000)
      constant := (30076343820602596265838569687249618768295780) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel017
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
  base := (-3661415678126619965704644952005201910657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1362820258353263819933731688760000000000000)
      constant := (7347024185794116303918305746866980425511228) }

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
  base := (-3677073139070645978648005587048163279771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-6202121980531700472932810117340000000000000)
      constant := (33879909365969557464949618472003519987241978) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel018
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
  base := (-7559188692664207321575010800383805276461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1436335242056572002178338472440000000000000)
      constant := (8223589720529003013932373365122387082906822) }

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
  base := (-118496368126448075710908109367471600203/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-6537023572957882192047129909660000000000000)
      constant := (37923923902002591088491993215492481555870528) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel019
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
  base := (-3876515438956575724375775182639741771053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1509850225759880184422945256120000000000000)
      constant := (9151581372458466120876627971942610612873612) }

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
  base := (-7772263149234740128633767695045549242643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-6871925165384063911161449701980000000000000)
      constant := (42204026698556177611038313125504912783994437) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel020
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
  base := (-7911940021739166834190823124206386889389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1583365209463188366667552039800000000000000)
      constant := (10130256094828074361668381943827774084839878) }

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
  base := (-3963473534491791970235940033063297171777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-7206826757810245630275769494300000000000000)
      constant := (46716992271303815991596483244838171894492686) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel021
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
  base := (-8041548416002123424458849464180140040709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-236697170452356649844594117640000000000000)
      constant := (1594151703290794354506309326121478039430074) }

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
  base := (-4026614620134567987940871586147347336657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-1077389764319489621341441326660000000000000)
      constant := (7351490692159344016675592568605434235581218) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel022
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
  base := (-814603994450023881070964887318848290371/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1730395176869804731156765607160000000000000)
      constant := (12237588836468699156570884079187528675436420) }

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
  base := (-8155111180821113307141082406519982106667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-7876629942662609068504409078940000000000000)
      constant := (56432589750672148757561830433404687890959853) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel023
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
  base := (-1645704511331642581954579384690994508427/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1803910160573112913401372390840000000000000)
      constant := (13365532256083869794899230126761412690870770) }

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
  base := (-8235552663166614869650619464819633087079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-8211531535088790787618728871260000000000000)
      constant := (61632151728289587283582812336394541808598161) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel024
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
  base := (-8291304959072668665431342266430892716421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1877425144276421095645979174520000000000000)
      constant := (14542665928634603348038494057729772513790742) }

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
  base := (-8296742921997654818249460234111904456611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-8546433127514972506733048663580000000000000)
      constant := (67058155325468545452508047993076650134634549) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel025
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
  base := (-8336102154325377427891358272700198583237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-1950940127979729277890585958200000000000000)
      constant := (15768821783867886223668451281775380538842774) }

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
  base := (-4170150629034842890583905668148694453167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-8881334719941154225847368455900000000000000)
      constant := (72709886430575868655288016283192851492306706) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel026
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
  base := (-8364188123593930841356286874351515903671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2024455111683037460135192741880000000000000)
      constant := (17043874971628314440657174289553551441440242) }

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
  base := (-4183712709021507548593402696871200432967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-9216236312367335944961688248220000000000000)
      constant := (78586816837334361355520237720279601218123106) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel027
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
  base := (-1675301848992798168814201861752328891501/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2097970095386345642379799525560000000000000)
      constant := (18367732746863493129056664719801358843164510) }

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
  base := (-1675800269079641926771590932775861512469/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-9551137904793517664076008040540000000000000)
      constant := (84688555844669093564614495398809225365005855) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel028
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
  base := (-1046721068045758764362636986119082150221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-310212154155664832089200901320000000000000)
      constant := (2820046601861747435191156668834662799175248) }

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
  base := (-130870068102977149538025684261098735823/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-1412291356745671340455761118980000000000000)
      constant := (13002116351020184573645783955699249897161664) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel029
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
  base := (-8356488279722008233366184630961532247391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2245000062792962006869013092920000000000000)
      constant := (21161604188858190913708545650105769839755682) }

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
  base := (-4178979597415127614739789844987168868263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-10220941089645881102304647625180000000000000)
      constant := (97565378905641233669986737846341317058192034) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel030
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
  base := (-4162528215071375058469657372015366653207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2318515046496270189113619876600000000000000)
      constant := (22631528652388497129255653782084988135971428) }

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
  base := (-2081546105378600756125016147200435933969/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-10555842682072062821418967417500000000000000)
      constant := (104340091061946823705657848583338431012478684) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel031
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
  base := (-8279761229220975265248840397450990600193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2392030030199578371358226660280000000000000)
      constant := (24150071356731068102015842369189802921181086) }

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
  base := (-1035078160628176403299251409605212711831/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-10890744274498244540533287209820000000000000)
      constant := (111338833952403410373067399361532809552660232) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel032
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
  base := (-1027602102136442075617837028535801026947/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2465545013902886553602833443960000000000000)
      constant := (25717211316152688245177613816987931994873552) }

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
  base := (-4110739003574976124281542919767620962989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-11225645866924426259647607002140000000000000)
      constant := (118561521043203071137905255437244958310643702) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel033
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
  base := (-2037095573814298257578679460115602197307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2539059997606194735847440227640000000000000)
      constant := (27332932938706087187100172236294683938655656) }

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
  base := (-8148887755705404426446946684772001459189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-11560547459350607978761926794460000000000000)
      constant := (126008088315338342154242527452595547356497651) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel034
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
  base := (-503910992551330072993777384717505060981/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2612574981309502918092047011320000000000000)
      constant := (28997224639115137938383035400802952064381792) }

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
  base := (-4031480968149966357225908882515317475281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-11895449051776789697876246586780000000000000)
      constant := (133678488402936022677186070644541489986802158) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel035
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
  base := (-7963485420452100117775567893032284467487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-383727137858973014333807685000000000000000)
      constant := (4387153972629478169602683379997548017455182) }

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
  base := (-1592756004678234896854220288434598250859/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-1747192949171853059570080911300000000000000)
      constant := (20224669465394327803688442081643101550979415) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel036
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
  base := (-7851176200287779732857797775941280682013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2759604948716119282581260578680000000000000)
      constant := (32471486048538178208021483322997754493162726) }

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
  base := (-1962850207916604784719239425528349568477/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-12565252236629153136104886171420000000000000)
      constant := (149690655942534063373430876679687991361206572) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel037
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
  base := (-3862848373611763485839465105171581591227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2833119932419427464825867362360000000000000)
      constant := (34281444603874900718855017754046370008119508) }

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
  base := (-1545173578837520788061921674768657313589/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-12900153829055334855219205963740000000000000)
      constant := (158032378259177014587461679142515110623536255) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel038
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
  base := (-7587083138172368233661545930091560178581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2906634916122735647070474146040000000000000)
      constant := (36139949938879038132575974041211027102499062) }

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
  base := (-3793606720117297066064530958227586364309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-13235055421481516574333525756060000000000000)
      constant := (166597838994576727695501538229523268826679462) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel039
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
  base := (-929420275129251726142720240810085570587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-2980149899826043829315080929720000000000000)
      constant := (38046999424416418840731412719344892912659792) }

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
  base := (-1858865334360514881638884937008595169769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-13569957013907698293447845548380000000000000)
      constant := (175387027623106313310361336295336838120527484) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel040
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
  base := (-1817638473104148236520071630385305077719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3053664883529352011559687713400000000000000)
      constant := (40002591104739446177021184372888960409534152) }

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
  base := (-908828658487409070167201196688167257243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-13904858606333880012562165340700000000000000)
      constant := (184399936346964402286993954982084145916446696) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel041
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
  base := (-7092673063846493958668151977559237345531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3127179867232660193804294497080000000000000)
      constant := (42006723524398534086654567840139194740137962) }

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
  base := (-709273033767002750563307526475934741491/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-14239760198760061731676485133020000000000000)
      constant := (193636559386376861352700802782261127790024690) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel042
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
  base := (-1380346154749102451155508458580420677481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-457242121562281196578414468680000000000000)
      constant := (6294199371381192374223155584179370552576330) }

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
  base := (-6901774267257673953366005610860123684209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-2082094541598034778684400703620000000000000)
      constant := (29013841779228816190937337908555812207894833) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel043
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
  base := (-6697735262003480279741310801549405751793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3274209834639276558293508064440000000000000)
      constant := (46160606523039680196395128493508158236324286) }

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
  base := (-6697768272128951184010691995033811643037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-14909563383612425169905124717660000000000000)
      constant := (212780932369618126216327480214970089065420683) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel044
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
  base := (-1620173168481715522617706260108218932067/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3347724818342584740538114848120000000000000)
      constant := (48310355692272501339282372034277578178629736) }

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
  base := (-3240358856999900268196506616693214613991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-15244464976038606889019444509980000000000000)
      constant := (222688676766909369861576934789596584710459938) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel045
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
  base := (-6250607598023979090996416701275315800123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3421239802045892922782721631800000000000000)
      constant := (50508642657692994550726847205775019051587946) }

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
  base := (-1562656645643230059836048727330105618141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-15579366568464788608133764302300000000000000)
      constant := (232820123887016554353395158601489693689599276) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel046
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
  base := (-6007483465508159976675690722675793584967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3494754785749201105027328415480000000000000)
      constant := (52755467083042253618583508724017772228673234) }

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
  base := (-6007497851874652671854631197740160157283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-15914268160890970327248084094620000000000000)
      constant := (243175272418394062702647387819516589370638197) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel047
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
  base := (-5751322847084846761270545502974975395467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3568269769452509287271935199160000000000000)
      constant := (55050828716391145225503690545968452411244234) }

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
  base := (-5751333743843380786305370145205344139491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-16249169753317152046362403886940000000000000)
      constant := (253754121381167068027333580255144443234484469) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel048
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
  base := (-1096425534688175515784730706191071529803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3641784753155817469516541982840000000000000)
      constant := (57394727368532359234341410767726374950396530) }

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
  base := (-219285436932773519090915075040719319751/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-16584071345743333765476723679260000000000000)
      constant := (264556670041141027400445514788556069499745225) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel049
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
  base := (-324993712441198545847370971471636479629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-530757105265589378823021252360000000000000)
      constant := (8541023270989509866187460451010353428563104) }

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
  base := (-1299976410574323346368102658957227038897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-2416996134024216497798720495940000000000000)
      constant := (39368988263740892518703966013202778786197956) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel050
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
  base := (-2452319561967394176787518661538870537191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3788814720562433834005755550200000000000000)
      constant := (62228135193774260387832766427338381374710564) }

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
  base := (-4904643846652548315692270915728239696781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-17253874530595697203705363263900000000000000)
      constant := (286832864379171720843368682091163846293719579) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel051
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
  base := (-919269536803818775385736686822796894963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3862329704265742016250362333880000000000000)
      constant := (64717644177152197826983575571196829521468130) }

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
  base := (-229817562755536443975723482194695391877/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-17588776123021878922819683056220000000000000)
      constant := (298306509323139445922560607524462786643644860) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel052
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
  base := (-2137512859217130670373506318203829733181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-3935844687969050198494969117560000000000000)
      constant := (67255689784426408913126092990192049372296524) }

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
  base := (-4275028417687647668797667919362410188289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-17923677715448060641934002848540000000000000)
      constant := (310003852435532449515493868847641177106964551) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel053
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
  base := (-3940673719431465614067269699442853616837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4009359671672358380739575901240000000000000)
      constant := (69842271967356278509094668696914600345549974) }

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
  base := (-78813515178875978378983974924999702393/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-18258579307874242361048322640860000000000000)
      constant := (321924893529119553664353832205883756562234350) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel054
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
  base := (-359329206952996164827734877942757738053/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4082874655375666562984182684920000000000000)
      constant := (72477390688454919629653289064056097416708060) }

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
  base := (-3593293610006340196392020939601970536089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-18593480900300424080162642433180000000000000)
      constant := (334069632457873681882347972761755530993584751) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel055
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
  base := (-404110133641604924652686688496196766179/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4156389639078974745228789468600000000000000)
      constant := (75161045918282829459325218215718981735315664) }

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
  base := (-3232882232282108531730299883705887370573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-18928382492726605799276962225500000000000000)
      constant := (346438069106514419038979853580785703669577307) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel056
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
  base := (-2859440957067588325529600937699616363711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-604272088968897561067628036040000000000000)
      constant := (11127605376204987718653818034392205370908046) }

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
  base := (-142972091751197569378828147860371141043/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-2751897726450398216913040288260000000000000)
      constant := (51290029054680179914748192869855932362285820) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel057
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
  base := (-1236485962934972644777404007137683528363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4303419606485591109718003035960000000000000)
      constant := (80673965815042671131485205718461014028440852) }

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
  base := (-61824314708740654534342411659932954031/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-19598185677578969237505601810140000000000000)
      constant := (371846035211592271954028149425298782690893160) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel058
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
  base := (-64796066661306454892715862388529184963/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4376934590188899291962609819640000000000000)
      constant := (83503230447659154927858216948709572475956032) }

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
  base := (-2073474632896113744494275926206629999167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-19933087270005150956619921602460000000000000)
      constant := (384885564530986548144716945787622876170367353) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel059
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
  base := (-830473855063296524337334016908453858569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4450449573892207474207216603320000000000000)
      constant := (86381031518428390169329100633225943043720476) }

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
  base := (-830474043492110317717561187302843094043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-20267988862431332675734241394780000000000000)
      constant := (398148791288764612283006641098218892391054074) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel060
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
  base := (-308848191956855801889209662386407618673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4523964557595515656451823387000000000000000)
      constant := (89307369016466191248613339338344528213480184) }

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
  base := (-617696525970287112219944443068667085549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-20602890454857514394848561187100000000000000)
      constant := (411635715440241421698619784351213435630545782) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel061
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
  base := (-796809401921785210412015855022800641981/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4597479541298823838696430170680000000000000)
      constant := (92282242932398124324345470615747765537085862) }

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
  base := (-159361923211131562723829451650237714623/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-20937792047283696113962880979420000000000000)
      constant := (425346336946480873255325613383931225839256285) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel062
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
  base := (-172598848092018421794621061061088710127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4670994525002132020941036954360000000000000)
      constant := (95305653258014302333463288303192026612815108) }

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
  base := (-345197857531944221289291505568477623569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-21272693639709877833077200771740000000000000)
      constant := (439280655772995676440246598435924301368006071) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel063
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
  base := (29860568714671028950126304484119675649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-677787072672205743312234819720000000000000)
      constant := (14053942855144437967687130946031110701836344) }

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
  base := (59721076657979433942043759459295916541/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-3086799318876579936027360080580000000000000)
      constant := (64776953126968155609206459134431871285484166) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel064
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
  base := (298555221975051484371876245120735210919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4818024492408748385430250521720000000000000)
      constant := (101498083109797299724882035152683664101340124) }

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
  base := (149277588103847255041109366879422611117/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-21942496824562241271305840356380000000000000)
      constant := (467820385265569067594643640313895301486010388) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel065
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
  base := (21756134992386262606450935952327628061/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4891539476112056567674857305400000000000000)
      constant := (104667102623348855341357684510666405377498900) }

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
  base := (543903340350288314020627338682575051883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-22277398416988422990420160148700000000000000)
      constant := (482425795877323607033929745439218031195760806) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel066
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
  base := (1591531135060790656232166497835712525929/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-4965054459815364749919464089080000000000000)
      constant := (107884658521098791276695001975227899827541042) }

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
  base := (318306216636476479921367915479238351283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-22612300009414604709534479941020000000000000)
      constant := (497254903699790497154572233806151720564579015) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel067
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
  base := (2108283547286759165097429647293092016889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5038569443518672932164070872760000000000000)
      constant := (111150750797854305445519219715894723017655122) }

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
  base := (263535438530540165209504093098688568249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-22947201601840786428648799733340000000000000)
      constant := (512307708710206868065756450109232173268782472) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel068
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
  base := (659515984120665206959263450405950795659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5112084427221981114408677656440000000000000)
      constant := (114465379448733571180580372053119132711898328) }

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
  base := (1319031953553382598404399831088615649817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-23282103194266968147763119525660000000000000)
      constant := (527584210887060903732411339126300159003138594) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel069
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
  base := (3180872255514254745518502109834527910649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5185599410925289296653284440120000000000000)
      constant := (117828544469117432873783070375503783735243602) }

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
  base := (3180872233416302307086756851432032784937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-23617004786693149866877439317980000000000000)
      constant := (543084410209910749586934893743501526458157217) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel070
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
  base := (373670845954806227539356168285885069781/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-751302056375513925556841603400000000000000)
      constant := (17320035122087458516876855688560023909769340) }

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
  base := (3736708442928392717715764615119943635449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-3421700911302761655141679872900000000000000)
      constant := (79829758094177794788297556907752556449033287) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel071
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
  base := (861114501151336902472375239946917365693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5332629378331905661142498007480000000000000)
      constant := (124700483601020816320945295466913989509189570) }

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
  base := (4305572493259713714337016308869269779691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-24286807971545513305106078902620000000000000)
      constant := (574755900216371300208823119228431347972843731) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel072
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
  base := (2443732176543901397633786994124044338333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5406144362035213843387104791160000000000000)
      constant := (128209257704320125753411711892608312690313268) }

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
  base := (4887464343692698077507552194159081132137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-24621709563971695024220398694940000000000000)
      constant := (590927190863334512515381211121304154779272417) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel073
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
  base := (5482383962081086916682908741697573124421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5479659345738522025631711574840000000000000)
      constant := (131766568160643025555209319958946362166193258) }

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
  base := (5482383955019287595381053412398458599809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-24956611156397876743334718487260000000000000)
      constant := (607322178582843446766332947416247720242515769) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel074
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
  base := (6090331294721259075602562465883027206001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5553174329441830207876318358520000000000000)
      constant := (135372414966264018501839598502496536666188098) }

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
  base := (380645705588391812823297266766199295613/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-25291512748824058462449038279580000000000000)
      constant := (623940863358217183912790247323622302229845328) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel075
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
  base := (3355653157159276045879972655753575266863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5626689313145138390120925142200000000000000)
      constant := (139026798117587507409636421718027700752305148) }

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
  base := (167782657758275882990759306902718209821/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-25626414341250240181563358071900000000000000)
      constant := (640783245173338670273374851621263949221242440) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel076
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
  base := (7345308985410023584970169653317394510231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5700204296848446572365531925880000000000000)
      constant := (142729717611138123925341670618265104662002638) }

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
  base := (734530898241444845628136191468864200193/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-25961315933676421900677677864220000000000000)
      constant := (657849324012616289953716370380297691122851130) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel077
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
  base := (1598467854735368196380785996067542387923/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-824817040078822107801448387080000000000000)
      constant := (20925881920507517493824153323304727967154610) }

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
  base := (7992339271426836548991675192179587820007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-3756602503728943374255999665220000000000000)
      constant := (96448442837278747094407098222047314032660441) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel078
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
  base := (4326198572936940936034736754005670351349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5847234264255062936854745493240000000000000)
      constant := (150281165611572981007690437879745111388864404) }

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
  base := (8652397144184165017071377613967662150343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-26631119118528785338906317448860000000000000)
      constant := (692652572703709330144690542031239739008301263) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel079
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
  base := (1865096513953781846312787363507411834983/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5920749247958371119099352276920000000000000)
      constant := (154129694112040440349763283853058631799141670) }

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
  base := (9325482568500165908175144265928713594719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-26966020710954967058020637241180000000000000)
      constant := (710389742526696447238254645523894562695271079) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel080
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
  base := (10011595514089262211093604143024822181369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-5994264231661679301343959060600000000000000)
      constant := (158026758941890279719756827038016432573774162) }

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
  base := (10011595513136762899237699441898127955689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-27300922303381148777134957033500000000000000)
      constant := (728350609316136589283070211445877074428458849) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel081
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
  base := (214214718969490211913627678648588645753/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6067779215364987483588565844280000000000000)
      constant := (161972360098147176956603312462518084364189700) }

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
  base := (10710735947759539693260027282790206927657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-27635823895807330496249276825820000000000000)
      constant := (746535173058652278692160673803330481255096737) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel082
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
  base := (571145192171694964802332003953370269127/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6141294199068295665833172627960000000000000)
      constant := (165966497577921038061553237788108605727488920) }

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
  base := (11422903842897304414517932255128391787083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-27970725488233512215363596618140000000000000)
      constant := (764943433741246719848331662365991620778103603) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel083
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
  base := (12148099170307691464123003752657433409599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6214809182771603848077779411640000000000000)
      constant := (170009171378403208823496098869420428474140702) }

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
  base := (3037024792476257341955509423453048828887/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-28305627080659693934477916410460000000000000)
      constant := (783575391351287455538004662024551178134156668) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel084
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
  base := (12886321901231729656064090168528641959547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-898332023782130290046055170760000000000000)
      constant := (24871483070980428830419278571079400987433658) }

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
  base := (12886321900929614447743148832074866695513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-4091504096155125093370319457540000000000000)
      constant := (114633006553784466944955056840980716601817319) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel085
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
  base := (13637572009104692185746629334600738659007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6361839150178220212566992979000000000000000)
      constant := (178240127930644487504629710713290872388582686) }

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
  base := (13637572008878048548502680694251305160877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-28975430265512057372706555995100000000000000)
      constant := (821510397304910141180725513978664825575946757) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel086
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
  base := (14401849467557640010131617781172419558957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6435354133881528394811599762680000000000000)
      constant := (182428410677163509872362558676594897116777786) }

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
  base := (7200924733693818811471973157693941299777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-29310331857938239091820875787420000000000000)
      constant := (840813445624918125161328911348406056226403314) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel087
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
  base := (7589577125462769131710765718277818879357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6508869117584836577056206546360000000000000)
      constant := (186665229733904895499285336528442452500353972) }

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
  base := (15179154250798038774608955541316509552839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-29645233450364420810935195579740000000000000)
      constant := (860340190825199009339157616338100580712801999) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel088
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
  base := (3193897266844100682962740881819542152963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6582384101288144759300813330040000000000000)
      constant := (190950585098419831799379383011451575654951870) }

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
  base := (15969486334124893012722217854180629075477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-29980135042790602530049515372060000000000000)
      constant := (880090632894734691399279637629373657422285357) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel089
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
  base := (670913827724263101733751675208283428869/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6655899084991452941545420113720000000000000)
      constant := (195284476768323394896390192333400294400729050) }

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
  base := (16772845693034889550694470976192476965167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-30315036635216784249163835164380000000000000)
      constant := (900064771822794181284809110557720882341638647) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel090
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
  base := (3517846460775173910050450968807611226897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6729414068694761123790026897400000000000000)
      constant := (199666904741292211462639329671715729501179530) }

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
  base := (17589232303822125112702783222593058469911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-30649938227642965968278154956700000000000000)
      constant := (920262607598923175651108122250163538785230751) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel091
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
  base := (9209323071712966174353304799951469685387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-971847007485438472290661954440000000000000)
      constant := (29156838430723177383373887374818641151190836) }

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
  base := (18418646143385645094985382605254595880503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-4426405688581306812484639249860000000000000)
      constant := (134383448601847736216845390179991039540471689) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel092
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
  base := (19261087189238267476848166886750031457111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6876444036101377488279240464760000000000000)
      constant := (208577369587426672710061686641861503082796878) }

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
  base := (2407635898651008929397418183464917441249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-31319741412495329406506794541340000000000000)
      constant := (961329369654896951159735888254544228732726472) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel093
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
  base := (20116555419357865880384699833616900446389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-6949959019804685670523847248440000000000000)
      constant := (213105406456233913654652116492754456243746122) }

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
  base := (1257284713708452251775553416695857895333/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-31654643004921511125621114333660000000000000)
      constant := (982198295915129780442312357873985973309469648) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel094
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
  base := (20985050812373707076525294219629090658359/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-7023474003507993852768454032120000000000000)
      constant := (217681979619385684510074991582763650884519182) }

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
  base := (20985050812356749497376498837345231310127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-31989544597347692844735434125980000000000000)
      constant := (1003290918984190659650258981705789247007766007) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel095
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
  base := (10933286673700074744507943273912514487357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-7096988987211302035013060815800000000000000)
      constant := (222307089074835192401857413689186852839521972) }

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
  base := (21866573347387443821177574483890823784559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-32324446189773874563849753918300000000000000)
      constant := (1024607238852869229686356785508895853288990519) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel096
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
  base := (227611230040591531404994233417733638337/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-7170503970914610217257667599480000000000000)
      constant := (226980734820585389412218391571333789655702600) }

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
  base := (22761123004049634308178896515548514500231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-32659347782200056282964073710620000000000000)
      constant := (1046147255512178931601595534658076894894601871) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel097
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
  base := (23668699762463282630343005452405138589599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 980000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (57178320658128586190249720640000000000000)
      linear := (-7244018954617918399502274383160000000000000)
      constant := (231702916854687306871895901112595703581780702) }

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
  base := (23668699762456152074468672890833098016937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5453)
      previous := (0)
      next := (2926)
      square := (257302442961578637856123742880000000000000)
      linear := (-32994249374626238002078393502940000000000000)
      constant := (1067910968953349523918170128863037396225469217) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell227.Kernel098
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
  base := (3073662950399930475898229167255208586251/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 140000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (8168331522589798027178531520000000000000)
      linear := (-1045361991188746654535268738120000000000000)
      constant := (33781947882176923079150940565412583361660112) }

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
  base := (4917860720638820573689897475669560660487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (779)
      previous := (0)
      next := (418)
      square := (36757491851654091122303391840000000000000)
      linear := (-4761307281007488531598959042180000000000000)
      constant := (155699768452545702895875158223675911608053405) }

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
end ForestUnimodality.Stage80KernelData.Cell227.Kernel098
