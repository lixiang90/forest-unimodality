import ForestUnimodality.FiniteKernelDegreeCertificate
import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell320.Parameters
import ForestUnimodality.BinomialMassData.Q236_371.Batch000_049
import ForestUnimodality.BinomialMassData.Q236_371.Batch050_099
import ForestUnimodality.BinomialMassData.Q236_371.Batch100_149
import ForestUnimodality.BinomialMassData.Q9_14.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_14.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_14.Batch100_149

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree000.table
  base := (13791882255193371399339952173/1000000000000000000000000000)
  polynomial :=
    { denominator := 1855000000000000000000000000000000000000000
      center := (4484)
      previous := (0)
      next := (2565)
      square := (18512604544406091383254575567500000000000)
      linear := (-47564362071889189423345989715000000000000)
      constant := (25583941583383703945775611280915000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree000.table
  base := (13791882255193371399339952173/1000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-1794881587618459978239471310000000000000)
      constant := (965431757863535997953796652110000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree000.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel000

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree001.table
  base := (113873066302555828092293797118005021959299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-52768655347261128817915043704250000000000000)
      constant := (15701611469938073642994980493088569227499873659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree001.table
  base := (22723937077768407777018514547455451831213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-18851470769919967864630683325000000000000)
      constant := (5577462468944304287134206165642835698647185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree001.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel001

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (23957871187497746747/50000000000000000000)
  directionHi := (9583148474999098699/20000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree002.table
  base := (47030065143073921402989587428746081418327/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-35122277018590239541853681519985000000000000)
      constant := (6506832319435879735508210424073039392499946607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree002.table
  base := (46821842426263022338573978681233394428259/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-25138770426510715881585067480000000000000)
      constant := (4612778163049387576434775075035872653969382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree002.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel002

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23957871187497746747/50000000000000000000)
  centralHi := (9583148474999098699/20000000000000000000)
  directionLo := (16940773179473460707/25000000000000000000)
  directionHi := (67763092717893842829/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree003.table
  base := (4858161141446670498471216903343667041081/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-43860226363549914674749841187845000000000000)
      constant := (5408145504111035388863221042770145401611439368) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree003.table
  base := (77216718678806871091964339299453230985633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-31426070083101463898539451635000000000000)
      constant := (3826038376415237699975817813949458318296017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree003.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel003

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16940773179473460707/25000000000000000000)
  centralHi := (67763092717893842829/100000000000000000000)
  directionLo := (10374062534484152371/12500000000000000000)
  directionHi := (82992500275873218969/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree004.table
  base := (16064595942331291523139436383367327611787/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-52598175708509589807646000855705000000000000)
      constant := (4511661834713147676974514195367164679627948934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree004.table
  base := (31847089034893076084436990807561781685507/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-37713369739692211915493835790000000000000)
      constant := (3185657277944834725684615272661054605179686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree004.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel004

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10374062534484152371/12500000000000000000)
  centralHi := (82992500275873218969/100000000000000000000)
  directionLo := (23957871187497746747/25000000000000000000)
  directionHi := (95831484749990986989/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree005.table
  base := (53119117380281976721433076980771489131173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-122672250106938529881084321047130000000000000)
      constant := (7562579632080430323347633105031768535503782893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree005.table
  base := (52537712112497615095531631023170899639549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-44000669396282959932448219945000000000000)
      constant := (2665255672902831285756250040141624082337901) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree005.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel005

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23957871187497746747/25000000000000000000)
  centralHi := (95831484749990986989/100000000000000000000)
  directionLo := (107142857142857142857/100000000000000000000)
  directionHi := (53571428571428571429/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree006.table
  base := (43896256439052505200735348762511260986857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-140148148796857880146876640382850000000000000)
      constant := (6376728301157203653668353627549052473491984337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree006.table
  base := (43320436691569593935529496535054118793779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-50287969052873707949402604100000000000000)
      constant := (2243916239636015749306740357952651820895171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree006.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel006

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107142857142857142857/100000000000000000000)
  centralHi := (53571428571428571429/50000000000000000000)
  directionLo := (117369119465392738597/100000000000000000000)
  directionHi := (58684559732696369299/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree007.table
  base := (9062132899985957904674496553731356581019/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-11258860534769802172333497122755000000000000)
      constant := (387056930189006868238266203927939328905153194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree007.table
  base := (17846715497770460641897094173342097560377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-8082181244209207995193855465000000000000)
      constant := (272077408340398701926784303670539365845278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree007.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel007

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117369119465392738597/100000000000000000000)
  centralHi := (58684559732696369299/50000000000000000000)
  directionLo := (63386569104638743313/50000000000000000000)
  directionHi := (126773138209277486627/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree008.table
  base := (7474141374544064658783792738888597644641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-87549973088348290339230639527145000000000000)
      constant := (2325166008340732753374618279688970936812063762) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree008.table
  base := (5874344235090499833171057688698803249777/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-62862568366055203983311372410000000000000)
      constant := (1633168810544160977549448860651206796195365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree008.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel008

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63386569104638743313/50000000000000000000)
  centralHi := (126773138209277486627/100000000000000000000)
  directionLo := (135526185435787685657/100000000000000000000)
  directionHi := (67763092717893842829/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree009.table
  base := (12305786871665981194820107478703759693227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-96287922433307965472126799195005000000000000)
      constant := (2019921585490906006969322896993204187935457507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree009.table
  base := (4824495555315636032171328326431985910301/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-69149868022645952000265756565000000000000)
      constant := (1418388452838544717870664958352086548023745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree009.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel009

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135526185435787685657/100000000000000000000)
  centralHi := (67763092717893842829/50000000000000000000)
  directionLo := (143747227124986480483/100000000000000000000)
  directionHi := (35936806781246620121/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree010.table
  base := (10103043120970413766074713647777434986177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-105025871778267640605022958862865000000000000)
      constant := (1780763457205907765002919038109133928932388457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree010.table
  base := (19755350923758881960001250719040017822169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-75437167679236700017220140720000000000000)
      constant := (1250873641383147101320085556307960873286281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree010.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel010

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143747227124986480483/100000000000000000000)
  centralHi := (35936806781246620121/25000000000000000000)
  directionLo := (151522881682831612371/100000000000000000000)
  directionHi := (37880720420707903093/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree011.table
  base := (16526372241637783062568571146294547502293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-227527642246454631475838237061450000000000000)
      constant := (3194223592485195317426842555422367812763110813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree011.table
  base := (16114600116868108418913648395098427615619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-81724467335827448034174524875000000000000)
      constant := (1122993091671769816823312756376072953165331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree011.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel011

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151522881682831612371/100000000000000000000)
  centralHi := (37880720420707903093/25000000000000000000)
  directionLo := (620775543004659287/390625000000000000)
  directionHi := (158918539009192777473/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree012.table
  base := (3361566318631340081665649235857360741467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-122501770468186990870815278198585000000000000)
      constant := (1460283763197037946582046387128885979632518694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree012.table
  base := (6536347072124505739274321874810499055743/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-88011766992418196051128909030000000000000)
      constant := (1028497774333227309487132203931428907462814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree012.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel012

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620775543004659287/390625000000000000)
  centralHi := (158918539009192777473/100000000000000000000)
  directionLo := (10374062534484152371/6250000000000000000)
  directionHi := (165985000551746437937/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree013.table
  base := (339441580156933059722219708823326431207/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-131239719813146666003711437866445000000000000)
      constant := (1363147160996308146493372685127763573084202992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree013.table
  base := (10525107600217569331376072217758963527939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-94299066649008944068083293185000000000000)
      constant := (962265944489002510742565835296439212869011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree013.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel013

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10374062534484152371/6250000000000000000)
  centralHi := (165985000551746437937/100000000000000000000)
  directionLo := (86381333017484460561/50000000000000000000)
  directionHi := (172762666034968921123/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree014.table
  base := (4344381419465985597186051137488081698599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-19996809879729477305229656790615000000000000)
      constant := (185691160009664328105797826194548150439552137) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree014.table
  base := (8386089453035219303174218826667713173809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-14369480900799956012148239620000000000000)
      constant := (131442257369129407078964230971673992216663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree014.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel014

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86381333017484460561/50000000000000000000)
  centralHi := (172762666034968921123/100000000000000000000)
  directionLo := (35856858280031809199/20000000000000000000)
  directionHi := (44821072850039761499/25000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree015.table
  base := (6856041346923075533814653312131198704101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-297431237006132032539007514404330000000000000)
      constant := (2531061790763237006210970089063250320831165741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree015.table
  base := (6585220788914457766435994609054731868819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-106873665962190440101992061495000000000000)
      constant := (898536818842349648169836189049931861572131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree015.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel015

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35856858280031809199/20000000000000000000)
  centralHi := (44821072850039761499/25000000000000000000)
  directionLo := (185576872239522567163/100000000000000000000)
  directionHi := (46394218059880641791/25000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree016.table
  base := (5306201099411872589102148000218287385637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-314907135696051382804799833740050000000000000)
      constant := (2512500142945190764313885814108285294046462317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree016.table
  base := (202584529109552071245444479322521905463/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-113160965618781188118946445650000000000000)
      constant := (894752465638626242532586460530089334192175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree016.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel016

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185576872239522567163/100000000000000000000)
  centralHi := (46394218059880641791/25000000000000000000)
  directionLo := (191662969499981973977/100000000000000000000)
  directionHi := (95831484749990986989/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree017.table
  base := (997901411451876811330019610578028312699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-166191517192985366535296076537885000000000000)
      constant := (1268717283992692989458984480209040789976406118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree017.table
  base := (3776627545503466120578860353897677490613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-119448265275371936135900829805000000000000)
      constant := (906408419996501156532910612097236197040037) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree017.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel017

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (191662969499981973977/100000000000000000000)
  centralHi := (95831484749990986989/50000000000000000000)
  directionLo := (197561666941990442357/100000000000000000000)
  directionHi := (98780833470995221179/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree018.table
  base := (2872928184946720493996026973207178021559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-349858933075890083336384472411490000000000000)
      constant := (2600452085644910516838067488136089190065402319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree018.table
  base := (2682014817785785747170430575957624619141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-125735564931962684152855213960000000000000)
      constant := (931581484619263803328711995616923606337909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree018.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel018

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197561666941990442357/100000000000000000000)
  centralHi := (98780833470995221179/50000000000000000000)
  directionLo := (40657855630736305697/20000000000000000000)
  directionHi := (101644639076840764243/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree019.table
  base := (239708154684363157838563586426042156933/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-183667415882904716801088395873605000000000000)
      constant := (1348539442260958453009507896967807474089660212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree019.table
  base := (437100218086323265082157753719100401403/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-132022864588553432169809598115000000000000)
      constant := (968685325067131270491463221005193678674988) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree019.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel019

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40657855630736305697/20000000000000000000)
  centralHi := (101644639076840764243/50000000000000000000)
  directionLo := (10442993940866747043/5000000000000000000)
  directionHi := (208859878817334940861/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree020.table
  base := (274730320750581681212815812631690345759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-192405365227864391933984555541465000000000000)
      constant := (1411806519147220827595950798739676981761229038) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree020.table
  base := (1898099620113152768654977851239939813/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-138310164245144180186763982270000000000000)
      constant := (1016409882282958385910591623755378525418500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree020.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel020

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10442993940866747043/5000000000000000000)
  centralHi := (208859878817334940861/100000000000000000000)
  directionLo := (107142857142857142857/50000000000000000000)
  directionHi := (42857142857142857143/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree021.table
  base := (98603568810371054697306424472645243709/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-28734759224689152438125816458475000000000000)
      constant := (212641973130673348984900923115471246854100134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree021.table
  base := (130927241336625715243239375018739437223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-20656780557390704029102623775000000000000)
      constant := (153381700857524617062964493074012352121122) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree021.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel021

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107142857142857142857/50000000000000000000)
  centralHi := (42857142857142857143/20000000000000000000)
  directionLo := (109788758206709982677/50000000000000000000)
  directionHi := (43915503282683993071/20000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree022.table
  base := (-107169351820592477820710315678021372029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-209881263917783742199776874877185000000000000)
      constant := (1577329316916671597097950941389961460332556411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree022.table
  base := (-331488357489492960448533731105321382659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-150884763558325676220672750580000000000000)
      constant := (1139574537089717324278490127550839252249709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree022.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel022

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109788758206709982677/50000000000000000000)
  centralHi := (43915503282683993071/20000000000000000000)
  directionLo := (224744753179318188641/100000000000000000000)
  directionHi := (112372376589659094321/50000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree023.table
  base := (-29707551829840985772807079043047570693/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-437238426525486834665346069090090000000000000)
      constant := (3354513121756357153123068044950977233056119675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree023.table
  base := (-423076279531103210130900761068953557229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-157172063214916424237627134735000000000000)
      constant := (1213374256961196468466379254641492551391558) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree023.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel023

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224744753179318188641/100000000000000000000)
  centralHi := (112372376589659094321/50000000000000000000)
  directionLo := (114897913872467231837/50000000000000000000)
  directionHi := (9191833109797378547/4000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree024.table
  base := (-1203402705921365456579437868175190349139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-454714325215406184931138388425810000000000000)
      constant := (3574793865576439689170991294363778625154158901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree024.table
  base := (-1294734595405689694211699053227018323857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-163459362871507172254581518890000000000000)
      constant := (1294453838422430515486758485711876102131007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree024.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel024

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114897913872467231837/50000000000000000000)
  centralHi := (9191833109797378547/4000000000000000000)
  directionLo := (46947647786157095439/20000000000000000000)
  directionHi := (58684559732696369299/25000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree025.table
  base := (-1607111993500913925160720097635490090739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-472190223905325535196930707761530000000000000)
      constant := (3814037526835340101466596518528353508420593301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree025.table
  base := (-843852876017449773153287830779844315001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-169746662528097920271535903045000000000000)
      constant := (1382300188483186583903218703239825257129902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree025.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel025

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46947647786157095439/20000000000000000000)
  centralHi := (58684559732696369299/25000000000000000000)
  directionLo := (14973669492186091717/6250000000000000000)
  directionHi := (239578711874977467473/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree026.table
  base := (-981341106075424793646823644686056164331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-244833061297622442731361513548625000000000000)
      constant := (2035511920930445886163030546043886543485316829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree026.table
  base := (-406756575784549735402790105636339982183/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-176033962184688668288490287200000000000000)
      constant := (1476486181494791951392851467354096704365165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree026.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel026

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14973669492186091717/6250000000000000000)
  centralHi := (239578711874977467473/100000000000000000000)
  directionLo := (122161652689193354907/50000000000000000000)
  directionHi := (48864661075677341963/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree027.table
  base := (-2277516481855395357329002877721242736779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-507142021285164235728515346432970000000000000)
      constant := (4344733837815346275595228832356570428467001661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree027.table
  base := (-468046534021850111754049673470216686099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-182321261841279416305444671355000000000000)
      constant := (1576655749449285957806271967056046911905745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree027.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel027

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122161652689193354907/50000000000000000000)
  centralHi := (48864661075677341963/20000000000000000000)
  directionLo := (31122187603452457113/12500000000000000000)
  directionHi := (49795500165523931381/20000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree028.table
  base := (-2557805384705161296326855489570509232033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (475304)
      previous := (0)
      next := (271890)
      square := (1962336081707045686624985010155000000000000)
      linear := (-74945417139297655142043952252670000000000000)
      constant := (662045062398452850265675833351615076970535121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree028.table
  base := (-1306560821586907819628424942898658848231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-26944080213981452046057007930000000000000)
      constant := (240358804712182498743870363959418776124766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree028.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel028

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31122187603452457113/12500000000000000000)
  centralHi := (49795500165523931381/20000000000000000000)
  directionLo := (63386569104638743313/25000000000000000000)
  directionHi := (253546276418554973253/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree029.table
  base := (-2808732885964273545177590886418593707331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-542093818665002936260099985104410000000000000)
      constant := (4939055112619443214961273508803538343529253829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree029.table
  base := (-1428760863462951530428646720306437700317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-194895861154460912339353439665000000000000)
      constant := (1793805307591103053618519829836219105368934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree029.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel029

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63386569104638743313/25000000000000000000)
  centralHi := (253546276418554973253/100000000000000000000)
  directionLo := (258034169545549188859/100000000000000000000)
  directionHi := (12901708477277459443/5000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree030.table
  base := (-303464619955042408565541285439086741437/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-279784858677461143262946152220065000000000000)
      constant := (2629177255217660511418236837528593309109349415) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree030.table
  base := (-3077679527369380748860811203325412848301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-201183160811051660356307823820000000000000)
      constant := (1910328689572573116701381437012054770433251) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree030.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel030

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258034169545549188859/100000000000000000000)
  centralHi := (12901708477277459443/5000000000000000000)
  directionLo := (65611332395977984773/25000000000000000000)
  directionHi := (262445329583911939093/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree031.table
  base := (-20244975412736970352573520291048197319/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-288522808022420818395842311887925000000000000)
      constant := (2795855569326707913645504112061206805825241680) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree031.table
  base := (-819288962214943257198713293874617714391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-207470460467642408373262207975000000000000)
      constant := (2031907299516266988504832319166824927979364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree031.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel031

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65611332395977984773/25000000000000000000)
  centralHi := (262445329583911939093/100000000000000000000)
  directionLo := (10671342512561770607/4000000000000000000)
  directionHi := (33347945351755533147/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree032.table
  base := (-1712726364746031827036441171713868831939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-297260757367380493528738471555785000000000000)
      constant := (2969351202905166693324322408776931380103084101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree032.table
  base := (-1729470417023918571021779767176290607651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-213757760124233156390216592130000000000000)
      constant := (2158394620432297564201049607616723520450202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree032.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel032

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671342512561770607/4000000000000000000)
  centralHi := (33347945351755533147/12500000000000000000)
  directionLo := (135526185435787685657/50000000000000000000)
  directionHi := (54210474174315074263/20000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree033.table
  base := (-3596001936471148805754969495347194506703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-611997413424680337323269262447290000000000000)
      constant := (6298972407164045548517582660566396800902892377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree033.table
  base := (-3625549099778788505278969938775098509211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-220045059780823904407170976285000000000000)
      constant := (2289667436095249288373103359076270173048661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree033.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel033

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135526185435787685657/50000000000000000000)
  centralHi := (54210474174315074263/20000000000000000000)
  directionLo := (137627491914269239501/50000000000000000000)
  directionHi := (275254983828538479003/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree034.table
  base := (-187651224774298178691966341113353601611/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-314736656057299843794530790891505000000000000)
      constant := (3336110487025159136263398474034608969206603490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree034.table
  base := (-3779098443751302191692264139500997464723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-226332359437414652424125360440000000000000)
      constant := (2425621974417887082434625765759451124228573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree034.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel034

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137627491914269239501/50000000000000000000)
  centralHi := (275254983828538479003/100000000000000000000)
  directionLo := (8731074649824975957/3125000000000000000)
  directionHi := (447031022071038769/160000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree035.table
  base := (-3898362294878865949683302075041073015841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (475304)
      previous := (0)
      next := (271890)
      square := (1962336081707045686624985010155000000000000)
      linear := (-92421315829217005407836271588390000000000000)
      constant := (1008313512445117294626838711183867381289518417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree035.table
  base := (-245085940233419853959046352954814130577/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-33231379870572200063011392085000000000000)
      constant := (366595816098501901820659021662810817375376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree035.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel035

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8731074649824975957/3125000000000000000)
  centralHi := (447031022071038769/160000000000000000)
  directionLo := (28347335475692042041/10000000000000000000)
  directionHi := (283473354756920420411/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree036.table
  base := (-4033573154507330680947724672368796999497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-664425109494438388120646220454450000000000000)
      constant := (7456678826477551236358020529200726412192233423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree036.table
  base := (-2026943769692894525985790611956703954163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-238906958750596148458034128750000000000000)
      constant := (2711239727566947026848041757388243012492026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree036.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel036

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28347335475692042041/10000000000000000000)
  centralHi := (283473354756920420411/100000000000000000000)
  directionLo := (143747227124986480483/50000000000000000000)
  directionHi := (287494454249972960967/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree037.table
  base := (-2079988229943716883283748536952848757989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-340950504092178869193219269895085000000000000)
      constant := (3933746045296845288933923345680372944101636051) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree037.table
  base := (-2088955976709243199071049370699514616189/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-245194258407186896474988512905000000000000)
      constant := (2860766493937203692757015105277697567613478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree037.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel037

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143747227124986480483/50000000000000000000)
  centralHi := (287494454249972960967/100000000000000000000)
  directionLo := (36432510291255651817/12500000000000000000)
  directionHi := (291460082330045214537/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree038.table
  base := (-2139345589386997956584774851934821384787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-349688453437138544326115429562945000000000000)
      constant := (4145240181811748905018256067123679249776532533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree038.table
  base := (-4294529055597433311079161253918773779069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-251481558063777644491942897060000000000000)
      constant := (3014698054081816753619612709652980084825619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree038.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel038

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36432510291255651817/12500000000000000000)
  centralHi := (291460082330045214537/100000000000000000000)
  directionLo := (295372473259076180741/100000000000000000000)
  directionHi := (147686236629538090371/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree039.table
  base := (-4390667575062750841592518241798012771191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-716852805564196438918023178461610000000000000)
      constant := (8725512850294100247794066204293359724160499569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree039.table
  base := (-880931096955251496064857045821600873869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-257768857720368392508897281215000000000000)
      constant := (3172989492696958452648300263599957785902095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree039.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel039

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295372473259076180741/100000000000000000000)
  centralHi := (147686236629538090371/50000000000000000000)
  directionLo := (149616857611810083963/50000000000000000000)
  directionHi := (299233715223620167927/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree040.table
  base := (-899342740327486231460036427264313701217/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-734328704254115789183815497797330000000000000)
      constant := (9172478329398528051591868834409762989253954515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree040.table
  base := (-4509069708843320880187841027468521300279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-264056157376959140525851665370000000000000)
      constant := (3335602664856099053101869619454042456286329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree040.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel040

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149616857611810083963/50000000000000000000)
  centralHi := (299233715223620167927/100000000000000000000)
  directionLo := (303045763365663224743/100000000000000000000)
  directionHi := (37880720420707903093/12500000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree041.table
  base := (-183900702511540911349008685729844054021/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-751804602944035139449607817133050000000000000)
      constant := (9631282103338234448442723100891703364012388475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree041.table
  base := (-4608433710116294838248509581823676383093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-270343457033549888542806049525000000000000)
      constant := (3502505133425672659928965411506889857228443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree041.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel041

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303045763365663224743/100000000000000000000)
  centralHi := (37880720420707903093/12500000000000000000)
  directionLo := (306810451355921853309/100000000000000000000)
  directionHi := (30681045135592185331/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree042.table
  base := (-2346832840160537323007115287646996048609/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-54948607259568177836814295462055000000000000)
      constant := (721560245904675049945751773329197116696201233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree042.table
  base := (-4703311126446515635899201526374283273767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-39518679527162948079965776240000000000000)
      constant := (524809897164423399334476431240380017083631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree042.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel042

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306810451355921853309/100000000000000000000)
  centralHi := (30681045135592185331/10000000000000000000)
  directionLo := (38816187713007424751/12500000000000000000)
  directionHi := (310529501704059398009/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree043.table
  base := (-2392829334557454593665332449695913608949/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-393378200161936919990596227902245000000000000)
      constant := (5292046721123751581542907313485344754950650691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree043.table
  base := (-2397091224779995752914491628564473108513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-282918056346731384576714817835000000000000)
      constant := (3849071560937398055937214187576931635365726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree043.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel043

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38816187713007424751/12500000000000000000)
  centralHi := (310529501704059398009/100000000000000000000)
  directionLo := (314204534970325288821/100000000000000000000)
  directionHi := (157102267485162644411/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree044.table
  base := (-4873924322546826104634267986706113158569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-804232299013793190246984775140210000000000000)
      constant := (11077973220176215752889355845242263878741404271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree044.table
  base := (-976291555339752612913153322585779199021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-289205356003322132593669201990000000000000)
      constant := (4028691881020115451506735238086484096239855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree044.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel044

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314204534970325288821/100000000000000000000)
  centralHi := (157102267485162644411/50000000000000000000)
  directionLo := (620775543004659287/195312500000000000)
  directionHi := (63567415603677110989/20000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree045.table
  base := (-991765724326375085176856403971101876101/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-821708197703712540512777094475930000000000000)
      constant := (11583432402458695967752810428165667833357911295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree045.table
  base := (-1241371881286579024262146854615463229617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-295492655659912880610623586145000000000000)
      constant := (4212513069952225178587885414801619206995068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree045.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel045

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620775543004659287/195312500000000000)
  centralHi := (63567415603677110989/20000000000000000000)
  directionLo := (321428571428571428571/100000000000000000000)
  directionHi := (80357142857142857143/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree046.table
  base := (-5040685010567540316471830441246607772271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-839184096393631890778569413811650000000000000)
      constant := (12100427846322158027308578754004615659616847289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree046.table
  base := (-2523285724118660522534491100801334542921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-301779955316503628627577970300000000000000)
      constant := (4400520439820328385532879427856469214793742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree046.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel046

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321428571428571428571/100000000000000000000)
  centralHi := (80357142857142857143/25000000000000000000)
  directionLo := (5077818377713091889/1562500000000000000)
  directionHi := (324980376173637880897/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree047.table
  base := (-1279940555695161870661482988794931272503/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-428329997541775620522180866573685000000000000)
      constant := (6314461281514500038440919819640253729442829154) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree047.table
  base := (-1024993246625699993943783915845499743773/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-308067254973094376644532354455000000000000)
      constant := (4592701412953745691348210815024102562775615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree047.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel047

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5077818377713091889/1562500000000000000)
  centralHi := (324980376173637880897/100000000000000000000)
  directionLo := (164246889822384553463/50000000000000000000)
  directionHi := (328493779644769106927/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree048.table
  base := (-2598145446652972372980798904054595086069/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-437067946886735295655077026241545000000000000)
      constant := (6584442403871202195782969890510061477758376771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree048.table
  base := (-1300222978158693755917706057799231677567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-314354554629685124661486738610000000000000)
      constant := (4789045207744545910552930766991350591196868) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree048.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel048

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (164246889822384553463/50000000000000000000)
  centralHi := (328493779644769106927/100000000000000000000)
  directionLo := (10374062534484152371/3125000000000000000)
  directionHi := (331970001103492875873/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree049.table
  base := (-5270469153509742947528206552619324198561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (475304)
      previous := (0)
      next := (271890)
      square := (1962336081707045686624985010155000000000000)
      linear := (-127373113209055705939420910259830000000000000)
      constant := (1960041044208997225839963315123886228283695057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree049.table
  base := (-5274537283932198668088047099494987015049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-45805979183753696096920160395000000000000)
      constant := (712791796161586067507147869657285090894657) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree049.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel049

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10374062534484152371/3125000000000000000)
  centralHi := (331970001103492875873/100000000000000000000)
  directionLo := (335410196624968454461/100000000000000000000)
  directionHi := (167705098312484227231/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree050.table
  base := (-5342467371294497171949071828451344398387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-909087691153309291841738691154530000000000000)
      constant := (14283106618582266824523365221134128505661614933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree050.table
  base := (-5346064494363556921116153257412936863901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-326929153942866620695395506920000000000000)
      constant := (5194185563893618862450391088261766093668851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree050.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel050

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335410196624968454461/100000000000000000000)
  centralHi := (167705098312484227231/50000000000000000000)
  directionLo := (169407731794734607071/50000000000000000000)
  directionHi := (338815463589469214143/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree051.table
  base := (-5412432172740688548743649090968884642651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-926563589843228642107531010490250000000000000)
      constant := (14857322553339919619348618458489191748900873709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree051.table
  base := (-5415612927703729722891990931108681134059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-333216453599457368712349891075000000000000)
      constant := (5402967350227125963187293205891924624431109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree051.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel051

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (169407731794734607071/50000000000000000000)
  centralHi := (338815463589469214143/100000000000000000000)
  directionLo := (68437368954305622853/20000000000000000000)
  directionHi := (171093422385764057133/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree052.table
  base := (-1370122464661699023823239605292521804133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-472019744266573996186661664912985000000000000)
      constant := (7721458864783867757462080966481864012714659494) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree052.table
  base := (-5483302502029492229247126148033510132997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-339503753256048116729304275230000000000000)
      constant := (5615882056145861792124994705146358003483147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree052.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel052

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68437368954305622853/20000000000000000000)
  centralHi := (171093422385764057133/50000000000000000000)
  directionLo := (86381333017484460561/25000000000000000000)
  directionHi := (69105066413987568449/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree053.table
  base := (-1386687327696660113551295067583213335933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12985000000000000000000000000000000000000000
      center := (31388)
      previous := (0)
      next := (17955)
      square := (129588231810842639682782028972500000000000)
      linear := (-9070899879462899458859581595865000000000000)
      constant := (151319595855372491171516632821352789933163998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree053.table
  base := (-5549236471959023518980928897445612628673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-345791052912638864746258659385000000000000)
      constant := (5832924622173535574402326456551414981195023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree053.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel053

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86381333017484460561/25000000000000000000)
  centralHi := (69105066413987568449/20000000000000000000)
  directionLo := (21801991869776392483/6250000000000000000)
  directionHi := (348831869916422279729/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree054.table
  base := (-5611304467236287374959593510780498599587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-978991285912986692904907968497410000000000000)
      constant := (16648187916914437501294344473522741392254245733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree054.table
  base := (-44908030502389652638348553338873400759/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-352078352569229612763213043540000000000000)
      constant := (6054090688520134543621980130694400420351125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree054.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel054

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21801991869776392483/6250000000000000000)
  centralHi := (348831869916422279729/100000000000000000000)
  directionLo := (352107358396178215793/100000000000000000000)
  directionHi := (176053679198089107897/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree055.table
  base := (-709279554159120383501595425708477744677/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-498233592301453021585350143916565000000000000)
      constant := (8633919417445566566715727008477937658979652172) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree055.table
  base := (-2838090625750767846156719207790695289811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-358365652225820360780167427695000000000000)
      constant := (6279376495564961980033164546142761861598522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree055.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel055

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352107358396178215793/100000000000000000000)
  centralHi := (176053679198089107897/50000000000000000000)
  directionLo := (35535265610950712669/10000000000000000000)
  directionHi := (355352656109507126691/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree056.table
  base := (-5735615283659105154871712833690304696887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (475304)
      previous := (0)
      next := (271890)
      square := (1962336081707045686624985010155000000000000)
      linear := (-144849011898975056205213229595550000000000000)
      constant := (2556974324205599183418606224759467538745110919) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree056.table
  base := (-1434333749711565412177835340221208331663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-52093278840344444113874544550000000000000)
      constant := (929825542711408442117072895953806166713436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree056.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel056

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35535265610950712669/10000000000000000000)
  centralHi := (355352656109507126691/100000000000000000000)
  directionLo := (35856858280031809199/10000000000000000000)
  directionHi := (358568582800318091991/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree057.table
  base := (-1159100320644118235269334181650428114953/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1031418981982744743702284926504570000000000000)
      constant := (18541123881602602342196052397205867119148770635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree057.table
  base := (-5797022228515315393349158621269870332993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-370940251539001856814076196005000000000000)
      constant := (6742294797254386771707285157014026353683343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree057.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel057

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35856858280031809199/10000000000000000000)
  centralHi := (358568582800318091991/100000000000000000000)
  directionLo := (72351184354860566499/20000000000000000000)
  directionHi := (22609745110893927031/6250000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree058.table
  base := (-5853947805201061479984541494953802849671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1048894880672664093968077245840290000000000000)
      constant := (19194742457170089407152177093659543621968433889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree058.table
  base := (-1463823085368940990326942804454698980237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-377227551195592604831030580160000000000000)
      constant := (6979922069741158725977526032121878999873548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree058.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel058

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72351184354860566499/20000000000000000000)
  centralHi := (22609745110893927031/6250000000000000000)
  directionLo := (182457711063497155351/50000000000000000000)
  directionHi := (364915422126994310703/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree059.table
  base := (-5910999260670505247372041854839639281479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1066370779362583444233869565176010000000000000)
      constant := (19859669751222211097855840312149897209657948961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree059.table
  base := (-5912188047999145480871893758161354163479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-383514850852183352847984964315000000000000)
      constant := (7221658523636869589344281881226343645989529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree059.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel059

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (182457711063497155351/50000000000000000000)
  centralHi := (364915422126994310703/100000000000000000000)
  directionLo := (184023900399832159787/50000000000000000000)
  directionHi := (14721912031986572783/4000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree060.table
  base := (-372918454192320142063048811645918143917/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-541923339026251397249830942255865000000000000)
      constant := (10267950177409449873196160685262353446024961624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree060.table
  base := (-11655754481613122985770672323303825371/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-389802150508774100864939348470000000000000)
      constant := (7467502348562996869990572862952953629092352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree060.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel060

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184023900399832159787/50000000000000000000)
  centralHi := (14721912031986572783/4000000000000000000)
  directionLo := (371153744479045134327/100000000000000000000)
  directionHi := (46394218059880641791/12500000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree061.table
  base := (-6021069879684827515219857103774126456941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1101322576742422144765454203847450000000000000)
      constant := (21223429580559574833982795425464665460340183819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree061.table
  base := (-1505499764704510020690051338153174623131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-396089450165364848881893732625000000000000)
      constant := (7717451977618024740678105203988227773866324) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree061.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel061

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (371153744479045134327/100000000000000000000)
  centralHi := (46394218059880641791/12500000000000000000)
  directionLo := (93558477838783824891/25000000000000000000)
  directionHi := (74846782271027059913/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree062.table
  base := (-303707631299632400173126077009760314369/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-559399237716170747515623261591585000000000000)
      constant := (10961126682124871390632868473119595805699364710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree062.table
  base := (-1214994806321689418102853277220867230961/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-402376749821955596898848116780000000000000)
      constant := (7971506053947219226299108950655887528414555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree062.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel062

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93558477838783824891/25000000000000000000)
  centralHi := (74846782271027059913/20000000000000000000)
  directionLo := (188644466374917955133/50000000000000000000)
  directionHi := (377288932749835910267/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree063.table
  base := (-3062984560084696839139282142395418622083/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-81162455294447203235502774465635000000000000)
      constant := (1616597727166399601372502386924698883633981971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree063.table
  base := (-3063347601666609999911213060800043237307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-58380578496935192130828928705000000000000)
      constant := (1175666200288878915209878117452549394677702) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree063.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel063

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188644466374917955133/50000000000000000000)
  centralHi := (377288932749835910267/100000000000000000000)
  directionLo := (380319414627832459879/100000000000000000000)
  directionHi := (9507985365695811497/2500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree064.table
  base := (-3088270795980190033313020520243622302739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-576875136406090097781415580927305000000000000)
      constant := (11676885484537377386692325546288987582628701301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree064.table
  base := (-3088591683912619890995565878357221606471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-414951349135137092932756885090000000000000)
      constant := (8491923002945013113594202905840992282565842) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree064.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel064

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380319414627832459879/100000000000000000000)
  centralHi := (9507985365695811497/2500000000000000000)
  directionLo := (76665187799992789591/20000000000000000000)
  directionHi := (95831484749990986989/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree065.table
  base := (-6225889342352342721833447035350469513779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1171226171502099545828623481190330000000000000)
      constant := (24086459073878108575478902561449526025653944661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree065.table
  base := (-1245291311219652551886292819187094172109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-421238648791727840949711269245000000000000)
      constant := (8758283973196127287876134242255411927833295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree065.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel065

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76665187799992789591/20000000000000000000)
  centralHi := (95831484749990986989/25000000000000000000)
  directionLo := (386309065228284567119/100000000000000000000)
  directionHi := (4828863315353557089/1250000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree066.table
  base := (-62740291364514463151588114921917856249/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-594351035096009448047207900263025000000000000)
      constant := (12415215093586839106990580711651735217401569550) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree066.table
  base := (-1254906081978396795726739622327442268191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-427525948448318588966665653400000000000000)
      constant := (9028745546330249872036917357764776644293205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree066.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel066

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386309065228284567119/100000000000000000000)
  centralHi := (4828863315353557089/1250000000000000000)
  directionLo := (97317332810276517817/25000000000000000000)
  directionHi := (389269331241106071269/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree067.table
  base := (-395060971405137851603892602909803244001/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-603088984440969123180104059930885000000000000)
      constant := (12792841151888236625093404976246034173539666872) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree067.table
  base := (-3160709251813816652712012517044425494231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-433813248104909336983620037555000000000000)
      constant := (9303307057200740602651068882085896301565362) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree067.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel067

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97317332810276517817/25000000000000000000)
  centralHi := (389269331241106071269/100000000000000000000)
  directionLo := (196103627332747785891/50000000000000000000)
  directionHi := (392207254665495571783/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree068.table
  base := (-6366741224506284341741917150196273307697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1223653867571857596626000439197490000000000000)
      constant := (26352213680592382232361050820488714745655277223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree068.table
  base := (-3183566311047444305584881428792330272987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-440100547761500085000574421710000000000000)
      constant := (9581967928352905264021590233498351633247274) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree068.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel068

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196103627332747785891/50000000000000000000)
  centralHi := (392207254665495571783/100000000000000000000)
  directionLo := (197561666941990442357/50000000000000000000)
  directionHi := (79024666776796176943/20000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree069.table
  base := (-6411337195351309022029229254548194050437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1241129766261776946891792758533210000000000000)
      constant := (27130022801804797813347284187134212022703800883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree069.table
  base := (-6411683000116962465539949463397931553893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-446387847418090833017528805865000000000000)
      constant := (9864727658280406440234698555819751353859243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree069.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel069

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197561666941990442357/50000000000000000000)
  centralHi := (79024666776796176943/20000000000000000000)
  directionLo := (398018049021572356521/100000000000000000000)
  directionHi := (199009024510786178261/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree070.table
  base := (-645477303529918776573016567355702783743/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-89900404639406878368398934133495000000000000)
      constant := (1994222024912438420033050300223824080816306955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree070.table
  base := (-6455078529530457653051916526451435420399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-64667878153525940147783312860000000000000)
      constant := (1450226544469035799264149228139839952057207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree070.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel070

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398018049021572356521/100000000000000000000)
  centralHi := (199009024510786178261/50000000000000000000)
  directionLo := (200445931434318288513/50000000000000000000)
  directionHi := (400891862868636577027/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree071.table
  base := (-6497057081284385486700337658371877558551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1276081563641615647423377397204650000000000000)
      constant := (28719469173996405748499310680267276400963481809) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree071.table
  base := (-3248663469022007111415766330890632423337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-458962446731272329051437574175000000000000)
      constant := (10442542008703714365457460794838968022512974) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree071.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel071

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200445931434318288513/50000000000000000000)
  centralHi := (400891862868636577027/100000000000000000000)
  directionLo := (80749044348929022619/20000000000000000000)
  directionHi := (50468152718080639137/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree072.table
  base := (-6538196590672977389652016249800444503777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1293557462331534997689169716540370000000000000)
      constant := (29531104278560477460205301920207617018055629943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree072.table
  base := (-3269217471941600126726923537223419278519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-465249746387863077068391958330000000000000)
      constant := (10737595921348744916209769738352104910705138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree072.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel072

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (80749044348929022619/20000000000000000000)
  centralHi := (50468152718080639137/12500000000000000000)
  directionLo := (406578556307363056971/100000000000000000000)
  directionHi := (101644639076840764243/25000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree073.table
  base := (-6578197883114500237486901007754798349733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1311033361021454347954962035876090000000000000)
      constant := (30354012792623471125998125093828701800344400147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree073.table
  base := (-205575262174075006462838519566860086879/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-471537046044453825085346342485000000000000)
      constant := (11036747262934745408473264757295413383773728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree073.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel073

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406578556307363056971/100000000000000000000)
  centralHi := (101644639076840764243/25000000000000000000)
  directionLo := (40939228231163143241/10000000000000000000)
  directionHi := (409392282311631432411/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree074.table
  base := (-827133307933134801098800449267229537673/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-664254629855686849110377177605905000000000000)
      constant := (15594096979245742465142452777287277036820602428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree074.table
  base := (-6617252357712449899024178488152795366979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-477824345701044573102300726640000000000000)
      constant := (11339995784413980887257983082275513027018029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree074.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel074

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40939228231163143241/10000000000000000000)
  centralHi := (409392282311631432411/100000000000000000000)
  directionLo := (412186801321528816111/100000000000000000000)
  directionHi := (25761675082595551007/6250000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree075.table
  base := (-6654807128358953562376521765072319659647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1345985158401293048486546674547530000000000000)
      constant := (32033647115950985216904825837294680849726527273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree075.table
  base := (-6654971271262729051306518458327566043787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-484111645357635321119255110795000000000000)
      constant := (11647341269061735746224505657198199263854437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree075.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel075

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412186801321528816111/100000000000000000000)
  centralHi := (25761675082595551007/6250000000000000000)
  directionLo := (10374062534484152371/2500000000000000000)
  directionHi := (414962501379366094841/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree076.table
  base := (-6691424058645413410141013360328984867219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1363461057091212398752338993883250000000000000)
      constant := (32890371689545695175904841937165198193891109621) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree076.table
  base := (-1672892245094416173664518895909340139727/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-490398945014226069136209494950000000000000)
      constant := (11958783528220345060853821552761769332613508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree076.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel076

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10374062534484152371/2500000000000000000)
  centralHi := (414962501379366094841/100000000000000000000)
  directionLo := (417719757634669881721/100000000000000000000)
  directionHi := (208859878817334940861/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree077.table
  base := (-1681730224899989118883077445354059217009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-98638353984366553501295093801355000000000000)
      constant := (2411311941252589279644213450546506267231904066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree077.table
  base := (-6727048837691135024400172232401596603161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-70955177810116688164737697015000000000000)
      constant := (1753474628230106971367883710416938823777873) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree077.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel077

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417719757634669881721/100000000000000000000)
  centralHi := (208859878817334940861/50000000000000000000)
  directionLo := (16818357317441642973/4000000000000000000)
  directionHi := (210229466468020537163/50000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree078.table
  base := (-6761300830554558319753487481156459691911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1398412854471051099283923632554690000000000000)
      constant := (34637633142316216986027712302709423731545678049) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree078.table
  base := (-3380706881788262921786106125924961246113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-502973544327407565170118263260000000000000)
      constant := (12593957734134651058039668129154353797880926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree078.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel078

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16818357317441642973/4000000000000000000)
  centralHi := (210229466468020537163/50000000000000000000)
  directionLo := (211590189194266060901/50000000000000000000)
  directionHi := (423180378388532121803/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree079.table
  base := (-3397283312682774044775938103542339923981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-707944376580485224774857975945205000000000000)
      constant := (17764084601044618694421782354279868790523331179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree079.table
  base := (-6794666302748798134861123701060572653969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-509260843983998313187072647415000000000000)
      constant := (12917689413101018748095608546574281939955519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree079.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel079

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211590189194266060901/50000000000000000000)
  centralHi := (423180378388532121803/100000000000000000000)
  directionLo := (85176886775793387943/20000000000000000000)
  directionHi := (106471108469741734929/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree080.table
  base := (-6826720704943307544251309956000322724247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1433364651850889799815508271226130000000000000)
      constant := (36429975023638785267731453690048559579911918673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree080.table
  base := (-3413404336686242620430728679769985717077/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-515548143640589061204027031570000000000000)
      constant := (13245517325819789735955874236982541399726454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree080.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel080

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85176886775793387943/20000000000000000000)
  centralHi := (106471108469741734929/25000000000000000000)
  directionLo := (107142857142857142857/25000000000000000000)
  directionHi := (428571428571428571429/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree081.table
  base := (-6857765182901066651491901416495195197471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1450840550540809150081300590561850000000000000)
      constant := (37343050316045022036715426496605424837824894089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree081.table
  base := (-3428921404840746361091586631757013673981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-521835443297179809220981415725000000000000)
      constant := (13577441377513502649150577158604062659949862) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree081.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel081

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107142857142857142857/25000000000000000000)
  centralHi := (428571428571428571429/100000000000000000000)
  directionLo := (8624833627499188829/2000000000000000000)
  directionHi := (431241681374959441451/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree082.table
  base := (-3443850952618253008840001196595087886119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-734158224615364250173546454948785000000000000)
      constant := (19133697412611490469724553229745255508266694721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree082.table
  base := (-1377554079795812430461548512568395408391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-528122742953770557237935799880000000000000)
      constant := (13913461485504298650579125225095743124944205) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree082.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel082

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8624833627499188829/2000000000000000000)
  centralHi := (431241681374959441451/100000000000000000000)
  directionLo := (433895501385355434283/100000000000000000000)
  directionHi := (108473875346338858571/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree083.table
  base := (-6916532484836305495382650016403893516067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1485792347920647850612885229233290000000000000)
      constant := (39203008329173326474345314021049631692555022053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree083.table
  base := (-3458296456884003711072336141560550236991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-534410042610361305254890184035000000000000)
      constant := (14253577577639539859586952592203316076774882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree083.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel083

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433895501385355434283/100000000000000000000)
  centralHi := (108473875346338858571/25000000000000000000)
  directionLo := (218266594151393170979/50000000000000000000)
  directionHi := (436533188302786341959/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree084.table
  base := (-1736064582871831728059929757253238449621/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-107376303329326228634191253469215000000000000)
      constant := (2867849330989398942327562084414179144730204554) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree084.table
  base := (-6944311639659557861314347395956536714001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-77242477466707436181692081170000000000000)
      constant := (2085398512989182291288951485188304243001993) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree084.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel084

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218266594151393170979/50000000000000000000)
  centralHi := (436533188302786341959/100000000000000000000)
  directionLo := (439155032826839930709/100000000000000000000)
  directionHi := (43915503282683993071/10000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree085.table
  base := (-6970880677986342121505491734933217943893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1520744145300486551144469867904730000000000000)
      constant := (41108041569574376619516999271143856948984623587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree085.table
  base := (-6970927699621482183980200355852182400027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-546984641923542801288798952345000000000000)
      constant := (14946097470333086521892240447169493062398677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree085.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel085

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (439155032826839930709/100000000000000000000)
  centralHi := (43915503282683993071/10000000000000000000)
  directionLo := (220880658515231815169/50000000000000000000)
  directionHi := (441761317030463630339/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree086.table
  base := (-6996400602861032583662786599991505917229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1538220043990405901410262187240450000000000000)
      constant := (42077460987892072151236388672630809134046683211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree086.table
  base := (-6996442075050607887058148730800658596331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-553271941580133549305753336500000000000000)
      constant := (15298501167777526760846812783925767728779781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree086.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel086

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (220880658515231815169/50000000000000000000)
  centralHi := (441761317030463630339/100000000000000000000)
  directionLo := (444352314714165447311/100000000000000000000)
  directionHi := (27772019669635340457/6250000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree087.table
  base := (-702081905014661675496765265296896962823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-777847971340162625838027253288085000000000000)
      constant := (21529074379433360142103249270944449025700397285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree087.table
  base := (-7020855624089676302697441493309589956343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-559559241236724297322707720655000000000000)
      constant := (15655000641208602430611064206934080092139193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree087.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel087

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444352314714165447311/100000000000000000000)
  centralHi := (27772019669635340457/6250000000000000000)
  directionLo := (446928291741733075831/100000000000000000000)
  directionHi := (55866036467716634479/12500000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree088.table
  base := (-3522068423301694683759850705082196766203/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-786585920685122300970923412955945000000000000)
      constant := (22025052384351103645603203125101621354903052877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree088.table
  base := (-704416909755221957644435868119885047191/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-565846540893315045339662104810000000000000)
      constant := (16015595853836450456053226994341256326876410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree088.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel088

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446928291741733075831/100000000000000000000)
  centralHi := (55866036467716634479/12500000000000000000)
  directionLo := (224744753179318188641/50000000000000000000)
  directionHi := (449489506358636377283/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree089.table
  base := (-7066354716709384940842573579249083314819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1590647740060163952207639145247610000000000000)
      constant := (45053328917680652022934358366929256923464998021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree089.table
  base := (-883297894096320145357147007379140129229/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-572133840549905793356616488965000000000000)
      constant := (16380286773451786987899945633683627069342232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree089.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel089

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224744753179318188641/50000000000000000000)
  centralHi := (449489506358636377283/100000000000000000000)
  directionLo := (113009052373548141963/25000000000000000000)
  directionHi := (452036209494192567853/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree090.table
  base := (-3543736647859098074792753376050731467181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-804061819375041651236715732291665000000000000)
      constant := (23033910559182557365029479590341601270125739979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree090.table
  base := (-885937295705006968768396117306572565631/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-578421140206496541373570873120000000000000)
      constant := (16749073371835739646428867634690823554272648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree090.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel090

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113009052373548141963/25000000000000000000)
  centralHi := (452036209494192567853/100000000000000000000)
  directionLo := (227284322524247418557/50000000000000000000)
  directionHi := (90913729009698967423/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree091.table
  base := (-88843664262921681314251517732484328661/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-116114252674285903767087413137075000000000000)
      constant := (3363827235288140259160053903972706425821550280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree091.table
  base := (-7107515241096381435936039190364319190509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-83529777123298184198646465325000000000000)
      constant := (2445993660606637172122361372241199765666437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree091.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel091

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227284322524247418557/50000000000000000000)
  centralHi := (90913729009698967423/20000000000000000000)
  directionLo := (228543525082516518759/50000000000000000000)
  directionHi := (457087050165033037519/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree092.table
  base := (-445400921382537503430424285701017322677/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-821537718064961001502508051627385000000000000)
      constant := (24065304688658400851179131573979010197515320344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree092.table
  base := (-890804277778911374953225493023702401089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-590995739519678037407479641430000000000000)
      constant := (17498933508972452776992232707334708658773112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree092.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel092

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228543525082516518759/50000000000000000000)
  centralHi := (457087050165033037519/100000000000000000000)
  directionLo := (459591655489868927349/100000000000000000000)
  directionHi := (9191833109797378547/2000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree093.table
  base := (-1428847705828005544734382127054364703053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1660551334819841353270808422590490000000000000)
      constant := (49178905309005806416120700981480430939535410135) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree093.table
  base := (-1786063924556261586150175336798999186369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-597283039176268785424434025585000000000000)
      constant := (17880007006943884529570149270413646159471676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree093.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel093

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459591655489868927349/100000000000000000000)
  centralHi := (9191833109797378547/2000000000000000000)
  directionLo := (462082685418167671601/100000000000000000000)
  directionHi := (231041342709083835801/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree094.table
  base := (-7160964880476498289635235942315401198687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1678027233509760703536600741926210000000000000)
      constant := (50238469037019759450744135056082245863611522633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree094.table
  base := (-179024500281255547282627024204929112157/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-603570338832859533441388409740000000000000)
      constant := (18265176101394299315988506166053338940172280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree094.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel094

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462082685418167671601/100000000000000000000)
  centralHi := (231041342709083835801/50000000000000000000)
  directionLo := (464560358328831416121/100000000000000000000)
  directionHi := (232280179164415708061/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree095.table
  base := (-7176594129298523762980851362274833464153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1695503132199680053802393061261930000000000000)
      constant := (51309300515501013644632064650899729647160516927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree095.table
  base := (-717660746248117146551102437056418040243/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-609857638489450281458342793895000000000000)
      constant := (18654440777566153798784471397648605160280930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree095.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel095

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464560358328831416121/100000000000000000000)
  centralHi := (232280179164415708061/50000000000000000000)
  directionLo := (29189055425495581823/6250000000000000000)
  directionHi := (467024886807929309169/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree096.table
  base := (-7191126569278394118587509365762773014371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1712979030889599404068185380597650000000000000)
      constant := (52391399704028221333352203397125286159528961189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree096.table
  base := (-449446144832861321114412076547153175729/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-616144938146041029475297178050000000000000)
      constant := (19047801022454461560498053943347031910228464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree096.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel096

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29189055425495581823/6250000000000000000)
  centralHi := (467024886807929309169/100000000000000000000)
  directionLo := (469476477861570954391/100000000000000000000)
  directionHi := (58684559732696369299/12500000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree097.table
  base := (-7204562459579420618950995450026753087297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1730454929579518754333977699933370000000000000)
      constant := (53484766566929885191423368883132267678311353623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree097.table
  base := (-3602286404990404565277529049146102250751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-622432237802631777492251562205000000000000)
      constant := (19445256824583581448236981545339931979426402) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree097.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel097

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469476477861570954391/100000000000000000000)
  centralHi := (58684559732696369299/12500000000000000000)
  directionLo := (471915333118826582193/100000000000000000000)
  directionHi := (235957666559413291097/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree098.table
  base := (-1443380405841019791007916141190204438857/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (475304)
      previous := (0)
      next := (271890)
      square := (1962336081707045686624985010155000000000000)
      linear := (-249704404038491157799967145609870000000000000)
      constant := (7798485867526533581206428186814325050593774045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree098.table
  base := (-225528473356213309567018423230045131191/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-89817076779888932215600849480000000000000)
      constant := (2835258310544691072762957978081469890613216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree098.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel098

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471915333118826582193/100000000000000000000)
  centralHi := (235957666559413291097/50000000000000000000)
  directionLo := (474341649025256899799/100000000000000000000)
  directionHi := (2371708245126284499/500000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree099.table
  base := (-1807036370198089284922897747846547285883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-882703363479678727432781169302405000000000000)
      constant := (27852651596702310777901004330714446770047555994) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree099.table
  base := (-7228153512743239213308625565488050080313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-635006837115813273526160330515000000000000)
      constant := (20252455061167222764122464384767335546064663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree099.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel099

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474341649025256899799/100000000000000000000)
  centralHi := (2371708245126284499/500000000000000000)
  directionLo := (476755617027578332417/100000000000000000000)
  directionHi := (238377808513789166209/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree100.table
  base := (-7238292993920401533481665707663895548719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1782882625649276805131354657940530000000000000)
      constant := (56832472904369083110818549002479433752778768121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree100.table
  base := (-361915003419894203242899500587879945051/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-641294136772404021543114714670000000000000)
      constant := (20662197478689929296954526791423877653850020) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree100.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel100

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476755617027578332417/100000000000000000000)
  centralHi := (238377808513789166209/50000000000000000000)
  directionLo := (14973669492186091717/3125000000000000000)
  directionHi := (95831484749990986989/20000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree101.table
  base := (-7247344727997416136092990844700131522037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1800358524339196155397146977276250000000000000)
      constant := (57970910183638017879594224928013869197175305283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree101.table
  base := (-3623675479294486247371863528171170092921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-647581436428994769560069098825000000000000)
      constant := (21076035419313872718173291902005475330893742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree101.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel101

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14973669492186091717/3125000000000000000)
  centralHi := (95831484749990986989/20000000000000000000)
  directionLo := (240773625581188198549/50000000000000000000)
  directionHi := (481547251162376397099/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree102.table
  base := (-7255300824779320780341925100204366775561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1817834423029115505662939296611970000000000000)
      constant := (59120615011699999300420360010520770752645008399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree102.table
  base := (-7255306311669656377510382228550545536297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-653868736085585517577023482980000000000000)
      constant := (21493968876749748585926076985576023268721447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree102.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel102

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240773625581188198549/50000000000000000000)
  centralHi := (481547251162376397099/100000000000000000000)
  directionLo := (30245329796347004263/6250000000000000000)
  directionHi := (483925276741552068209/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree103.table
  base := (-145243228211355868726721915860005592687/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-917655160859517427964365807973845000000000000)
      constant := (30140793685585369057906685159104964255424215825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree103.table
  base := (-907770780263863295530118583014629076667/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-660156035742176265593977867135000000000000)
      constant := (21915997845388479338309815378484515401946536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree103.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel103

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30245329796347004263/6250000000000000000)
  centralHi := (483925276741552068209/100000000000000000000)
  directionLo := (24314583681236179757/5000000000000000000)
  directionHi := (486291673624723595141/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree104.table
  base := (-145358531962573444541726100558437641587/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-926393110204477103097261967641705000000000000)
      constant := (30726913623264515800341963019284942114358093325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree104.table
  base := (-7267930852236719441852782853606642382361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-666443335398767013610932251290000000000000)
      constant := (22342122320216189122965556612693274523264311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree104.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel104

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24314583681236179757/5000000000000000000)
  centralHi := (486291673624723595141/100000000000000000000)
  directionLo := (488646610756773419629/100000000000000000000)
  directionHi := (48864661075677341963/10000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree105.table
  base := (-3636298244183277115414780608388453175937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 98315000000000000000000000000000000000000000
      center := (237652)
      previous := (0)
      next := (135945)
      square := (981168040853522843312492505077500000000000)
      linear := (-133590151364205254032879732472795000000000000)
      constant := (4474095330277590722041886221199357845201550769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree105.table
  base := (-7272600233736722840213966453079488407617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-96104376436479680232555233635000000000000)
      constant := (3253191756677155172232823526722193581146681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree105.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel105

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488646610756773419629/100000000000000000000)
  centralHi := (48864661075677341963/10000000000000000000)
  directionLo := (61373781628872857231/12500000000000000000)
  directionHi := (490990253030982857849/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree106.table
  base := (-3638085585893398463848041165329499187717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 12985000000000000000000000000000000000000000
      center := (31388)
      previous := (0)
      next := (17955)
      square := (129588231810842639682782028972500000000000)
      linear := (-17808849224422574591755741263725000000000000)
      constant := (602189712177218921986775567557679290609498951) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree106.table
  base := (-22738045215577951176349546568963152543/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-679017934711948509644841019600000000000000)
      constant := (23206657770923843223264179185033657768125760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree106.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel106

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61373781628872857231/12500000000000000000)
  centralHi := (490990253030982857849/100000000000000000000)
  directionLo := (493322761423771638041/100000000000000000000)
  directionHi := (246661380711885819021/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree107.table
  base := (-3639325364886057133314490201641819295663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-952606958239356128495950446645285000000000000)
      constant := (32519075918012120168036428174053118350325649017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree107.table
  base := (-909831704023722928361278046188508606987/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-685305234368539257661795403755000000000000)
      constant := (23645068739131248606425995074350354626061096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree107.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel107

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493322761423771638041/100000000000000000000)
  centralHi := (246661380711885819021/50000000000000000000)
  directionLo := (495644293123730467289/100000000000000000000)
  directionHi := (49564429312373046729/10000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree108.table
  base := (-455002202231091546234835408736081997877/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-961344907584315803628846606313145000000000000)
      constant := (33127730824751985631597601338073495501841694744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree108.table
  base := (-7280037790396968551222465285482353162247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-691592534025130005678749787910000000000000)
      constant := (24087575198077061655693176223931364695049897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree108.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel108

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (495644293123730467289/100000000000000000000)
  centralHi := (49564429312373046729/10000000000000000000)
  directionLo := (31122187603452457113/6250000000000000000)
  directionHi := (497955001655239313809/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree109.table
  base := (-455020297243992864537102361139049934317/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-970082856929275478761742765981005000000000000)
      constant := (33742019461046575885710918652258620223925390424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree109.table
  base := (-291213080174578528509738271525174419287/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-697879833681720753695704172065000000000000)
      constant := (24534177144784142161363293556007911336373425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree109.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel109

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31122187603452457113/6250000000000000000)
  centralHi := (497955001655239313809/100000000000000000000)
  directionLo := (500255036996946515033/100000000000000000000)
  directionHi := (250127518498473257517/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree110.table
  base := (-1455903870109855795729161447400580544423/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-1957641612548470307789277851297730000000000000)
      constant := (68723883645511588149543283799590483466425369285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree110.table
  base := (-7279521329325824425881093965916017731439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-704167133338311501712658556220000000000000)
      constant := (24984874576546045829729380211245115131159489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree110.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel110

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (500255036996946515033/100000000000000000000)
  centralHi := (250127518498473257517/50000000000000000000)
  directionLo := (251272272847683726137/50000000000000000000)
  directionHi := (20101781827814698091/4000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree111.table
  base := (-1819404768587960157756421395770976401401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-987558755619194829027535085316725000000000000)
      constant := (34987497906113906559778389714676994074269529918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree111.table
  base := (-7277620815656382266930049207844184705469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-710454432994902249729612940375000000000000)
      constant := (25439667490894381487052997242581884949432019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree111.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel111

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251272272847683726137/50000000000000000000)
  centralHi := (20101781827814698091/4000000000000000000)
  directionLo := (504823670973846276991/100000000000000000000)
  directionHi := (3943934929483174039/781250000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree112.table
  base := (-58196991817918591349360788229079687233/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (475304)
      previous := (0)
      next := (271890)
      square := (1962336081707045686624985010155000000000000)
      linear := (-284656201418329858331551784281310000000000000)
      constant := (10176767916481378856077475795137050763742190125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree112.table
  base := (-1818656377363687286949656642528076518571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-102391676093070428249509617790000000000000)
      constant := (3699793697938616732164376821609213857480012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree112.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel112

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504823670973846276991/100000000000000000000)
  centralHi := (3943934929483174039/781250000000000000)
  directionLo := (101418510567421989301/20000000000000000000)
  directionHi := (253546276418554973253/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree113.table
  base := (-7270534104919563038527061479916643472231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-2010069308618228358586654809304890000000000000)
      constant := (72511022448646039223297815420873473275838652929) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree113.table
  base := (-1454107090610110047864156354506428948639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-723029032308083745763521708685000000000000)
      constant := (26361539758499701110651437907022174907583445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree113.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel113

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101418510567421989301/20000000000000000000)
  centralHi := (253546276418554973253/50000000000000000000)
  directionLo := (254675664085815275229/50000000000000000000)
  directionHi := (509351328171630550459/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree114.table
  base := (-726534949937216554425515638205293237533/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1013772603654073854426223564320305000000000000)
      constant := (36897968453139326593515056558293766167463601735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree114.table
  base := (-726535068544785889637408769688389820111/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-729316331964674493780476092840000000000000)
      constant := (26828619107771333849166396638647688988145610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree114.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel114

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254675664085815275229/50000000000000000000)
  centralHi := (509351328171630550459/100000000000000000000)
  directionLo := (255800065420999756049/50000000000000000000)
  directionHi := (511600130841999512099/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree115.table
  base := (-3629535099643973447808212939823746114803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1022510552999033529559119723988165000000000000)
      constant := (37546059391471060086771058170727819761012400277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree115.table
  base := (-226845976334768624610570641898069947463/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-735603631621265241797430476995000000000000)
      constant := (27299793931617985218135107852460076322378016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree115.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel115

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255800065420999756049/50000000000000000000)
  centralHi := (511600130841999512099/100000000000000000000)
  directionLo := (513839091783505665171/100000000000000000000)
  directionHi := (128459772945876416293/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree116.table
  base := (-3625848120223260847371075309045224597011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1031248502343993204692015883656025000000000000)
      constant := (38199784036855849124690936748082826241242808949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree116.table
  base := (-7251697158311085872181656605456420041453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-741890931277855989814384861150000000000000)
      constant := (27775064228399805323948522089692635417968803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree116.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel116

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513839091783505665171/100000000000000000000)
  centralHi := (128459772945876416293/25000000000000000000)
  directionLo := (516068339091098377719/100000000000000000000)
  directionHi := (12901708477277459443/2500000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree117.table
  base := (-452701728503090932188361429924989420423/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1039986451688952879824912043323885000000000000)
      constant := (38859142387008745405024094053625456249468462856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree117.table
  base := (-3621614231703016861928691607357167725523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-748178230934446737831339245305000000000000)
      constant := (28254429996589821613102537091485247562898746) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree117.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel117

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516068339091098377719/100000000000000000000)
  centralHi := (12901708477277459443/2500000000000000000)
  directionLo := (259143999052453381683/50000000000000000000)
  directionHi := (518287998104906763367/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree118.table
  base := (-1446732895402298989376092382845992814601/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-2097448802067825109915616405983490000000000000)
      constant := (79048268879604360972331250198864353515027518795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree118.table
  base := (-3616832593557690502470384238563976690993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-754465530591037485848293629460000000000000)
      constant := (28737891234761254953940761780515730284282686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree118.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel118

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259143999052453381683/50000000000000000000)
  centralHi := (518287998104906763367/100000000000000000000)
  directionLo := (52049819149247653799/10000000000000000000)
  directionHi := (520498191492476537991/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree119.table
  base := (-7223006732215641751044817630478773627927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (475304)
      previous := (0)
      next := (271890)
      square := (1962336081707045686624985010155000000000000)
      linear := (-302132100108249208597344103617030000000000000)
      constant := (11484217198070974819805712726871535874154071399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree119.table
  base := (-361150367836939626901486668125111658949/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-108678975749661176266464001945000000000000)
      constant := (4175063991653774538593699718466234367747140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree119.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel119

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52049819149247653799/10000000000000000000)
  centralHi := (520498191492476537991/100000000000000000000)
  directionLo := (32668689957992324909/6250000000000000000)
  directionHi := (104539807865575439709/20000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree120.table
  base := (-1802813612184158323304809564900030830087/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1066200299723831905223600522327465000000000000)
      constant := (40871019645484142550317892973155989713031990466) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree120.table
  base := (-3605627498977958109750036683403537879863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-767040129904218981882202397770000000000000)
      constant := (29717100115777019314825531858426453287773426) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree120.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel120

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32668689957992324909/6250000000000000000)
  centralHi := (104539807865575439709/20000000000000000000)
  directionLo := (104978131833564775637/20000000000000000000)
  directionHi := (262445329583911939093/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree121.table
  base := (-3599203826018424542809085011388167442733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1074938249068791580356496681995325000000000000)
      constant := (41552912794757038839938966090584141245014787147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree121.table
  base := (-7198408135000023176222968470175947732507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-773327429560809729899156781925000000000000)
      constant := (30212847756175617302732975448977628561107157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree121.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel121

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104978131833564775637/20000000000000000000)
  centralHi := (262445329583911939093/50000000000000000000)
  directionLo := (527073166124950428439/100000000000000000000)
  directionHi := (13176829153123760711/2500000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree122.table
  base := (-1436893273227624012474997674367948403191/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-2167352396827502510978785683326370000000000000)
      constant := (84480879278827812644761375862104006069181937845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree122.table
  base := (-7184466790810171813052746224115857548777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-779614729217400477916111166080000000000000)
      constant := (30712690861648201872040366750893322980109927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree122.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel122

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (527073166124950428439/100000000000000000000)
  centralHi := (13176829153123760711/2500000000000000000)
  directionLo := (66155834117295369801/12500000000000000000)
  directionHi := (529246672938362958409/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree123.table
  base := (-1792357653443122393685286155712916137773/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1092414147758710930622289001331045000000000000)
      constant := (42933600177890314408188257989262577019761573014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree123.table
  base := (-7169430987164634808431786139605943663921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-785902028873991225933065550235000000000000)
      constant := (31216629431127637661504029168135558760467871) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree123.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel123

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66155834117295369801/12500000000000000000)
  centralHi := (529246672938362958409/100000000000000000000)
  directionLo := (265705645020798094723/50000000000000000000)
  directionHi := (531411290041596189447/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree124.table
  base := (-715330041651458264977603830042952008033/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1101152097103670605755185160998905000000000000)
      constant := (43632394408701486615686934860231930213311649235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree124.table
  base := (-7153300744797975922165640680972013674397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-792189328530581973950019934390000000000000)
      constant := (31724663463597931046893490629952371329954547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree124.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel124

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (265705645020798094723/50000000000000000000)
  centralHi := (531411290041596189447/100000000000000000000)
  directionLo := (10671342512561770607/2000000000000000000)
  directionHi := (533567125628088530351/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree125.table
  base := (-1427215158979580506453802188270886421401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-2219780092897260561776162641333530000000000000)
      constant := (88673644660868593969637387329456034610359724795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree125.table
  base := (-1784019020875964181644368265111060285573/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-798476628187172721966974318545000000000000)
      constant := (32236792958089192611164916138944482184027692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree125.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel125

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671342512561770607/2000000000000000000)
  centralHi := (533567125628088530351/100000000000000000000)
  directionLo := (107142857142857142857/20000000000000000000)
  directionHi := (267857142857142857143/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree126.table
  base := (-7117756768517078579855945862169222169587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 196630000000000000000000000000000000000000000
      center := (475304)
      previous := (0)
      next := (271890)
      square := (1962336081707045686624985010155000000000000)
      linear := (-319607998798168558863136422952750000000000000)
      constant := (12870538269068638093107529741418486584479410819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree126.table
  base := (-7117757022225386181041279548735282090287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 70000000000000000000000000000000000000000
      center := (171)
      previous := (0)
      next := (95)
      square := (698588850732305335217153795000000000000)
      linear := (-114966275406251924283418386100000000000000)
      constant := (4679002559096172859329854268263853025367991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree126.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel126

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107142857142857142857/20000000000000000000)
  centralHi := (267857142857142857143/50000000000000000000)
  directionLo := (107570574840095427597/20000000000000000000)
  directionHi := (268926437100238568993/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree127.table
  base := (-88729291951472903467993907058616531873/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1127365945138549631153873640002485000000000000)
      constant := (45762579241329205713408171984492298477458736280) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree127.table
  base := (-88729294739182415307445108592569018213/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-811051227500354218000883086855000000000000)
      constant := (33273338329459553841312792968123379448605040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree127.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel127

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107570574840095427597/20000000000000000000)
  centralHi := (268926437100238568993/50000000000000000000)
  directionLo := (134995748232365920431/25000000000000000000)
  directionHi := (21599319717178547269/4000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree128.table
  base := (-3538917787838101830578525211508456824889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1136103894483509306286769799670345000000000000)
      constant := (46483908227964094084107157568915404494165453151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree128.table
  base := (-7077835771702399809835528803095295361849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-817338527156944966017837471010000000000000)
      constant := (33797754204592148913499197061768330527269399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree128.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel128

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134995748232365920431/25000000000000000000)
  centralHi := (21599319717178547269/4000000000000000000)
  directionLo := (135526185435787685657/25000000000000000000)
  directionHi := (542104741743150742629/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree129.table
  base := (-3528116722234192297447888988267651973249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1144841843828468981419665959338205000000000000)
      constant := (47210870900455942275804660524744392114750034391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree129.table
  base := (-1764058404190073792138573945405159717891/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-823625826813535714034791855165000000000000)
      constant := (34326265538246252259510322620376838695293364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree129.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel129

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135526185435787685657/25000000000000000000)
  centralHi := (542104741743150742629/100000000000000000000)
  directionLo := (34013638658572216439/6250000000000000000)
  directionHi := (21768728741486218521/4000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree130.table
  base := (-879192122391541807902898712956021944781/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 688205000000000000000000000000000000000000000
      center := (1663564)
      previous := (0)
      next := (951615)
      square := (6868176285974659903187447535542500000000000)
      linear := (-1153579793173428656552562119006065000000000000)
      constant := (47943467257659717604675053598228280733993593516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree130.table
  base := (-879192141319344776587322803823387738267/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-829913126470126462051746239320000000000000)
      constant := (34858872329625786412660782676376232006599336) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree130.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel130

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34013638658572216439/6250000000000000000)
  centralHi := (21768728741486218521/4000000000000000000)
  directionLo := (13658087982837816509/2500000000000000000)
  directionHi := (546323519313512660361/100000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 236
  qDenominator := 371
  table := BinomialMassData.Q236_371.Degree131.table
  base := (-7009746195722204742429769500946529601243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1376410000000000000000000000000000000000000000
      center := (3327128)
      previous := (0)
      next := (1903230)
      square := (13736352571949319806374895071085000000000000)
      linear := (-2324635485036776663370916557347850000000000000)
      constant := (97363394596941130678088575084723458719155312237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q236_371.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 9
  qDenominator := 14
  table := BinomialMassData.Q9_14.Degree131.table
  base := (-7009746328795340896850731074455284763327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 490000000000000000000000000000000000000000
      center := (1197)
      previous := (0)
      next := (665)
      square := (4890121955126137346520076565000000000000)
      linear := (-836200426126717210068700623475000000000000)
      constant := (35395574577960983327176042455867941046596977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_14.Degree131.checked
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
end ForestUnimodality.Stage170KernelData.Cell320.Kernel131

namespace ForestUnimodality.Stage170KernelData.Cell320
open FiniteKernelRationalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem degreePropagationThreshold : row.degreePropagationCheck 131 interval.lo interval.hi = true := by
  decide +kernel

theorem degreePropagationTail (n : ℕ) (hn : 131 ≤ n) (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual n j q :=
  row.degreePropagationCheck_sound 131 interval.lo interval.hi degreePropagationThreshold
    (fun _q hq j => Kernel131.actual_residual_nonneg j hq) n hn q hq j
end ForestUnimodality.Stage170KernelData.Cell320

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel132
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  degreePropagationTail 132 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel132

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel133
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  degreePropagationTail 133 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel133

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel134
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  degreePropagationTail 134 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel134

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel135
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  degreePropagationTail 135 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel135

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel136
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  degreePropagationTail 136 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel136

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel137
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  degreePropagationTail 137 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel137

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel138
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  degreePropagationTail 138 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel138

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel139
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  degreePropagationTail 139 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel139

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel140
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  degreePropagationTail 140 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel140

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel141
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  degreePropagationTail 141 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel141

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel142
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  degreePropagationTail 142 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel142

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel143
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  degreePropagationTail 143 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel143

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel144
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  degreePropagationTail 144 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel144

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel145
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  degreePropagationTail 145 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel145

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel146
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  degreePropagationTail 146 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel146

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel147
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  degreePropagationTail 147 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel147

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel148
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  degreePropagationTail 148 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel148

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel149
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  degreePropagationTail 149 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel149

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel150
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  degreePropagationTail 150 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel150

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel151
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  degreePropagationTail 151 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel151

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel152
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  degreePropagationTail 152 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel152

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel153
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  degreePropagationTail 153 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel153

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel154
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  degreePropagationTail 154 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel154

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel155
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  degreePropagationTail 155 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel155

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel156
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  degreePropagationTail 156 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel156

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel157
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  degreePropagationTail 157 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel157

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel158
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  degreePropagationTail 158 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel158

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel159
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  degreePropagationTail 159 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel159

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel160
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  degreePropagationTail 160 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel160

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel161
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  degreePropagationTail 161 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel161

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel162
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  degreePropagationTail 162 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel162

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel163
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  degreePropagationTail 163 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel163

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel164
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  degreePropagationTail 164 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel164

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel165
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  degreePropagationTail 165 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel165

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel166
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  degreePropagationTail 166 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel166

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel167
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  degreePropagationTail 167 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel167

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel168
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  degreePropagationTail 168 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel168

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel169
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  degreePropagationTail 169 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel169

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel170
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 170 j q :=
  degreePropagationTail 170 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel170

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel171
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 171 j q :=
  degreePropagationTail 171 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel171

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel172
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 172 j q :=
  degreePropagationTail 172 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel172

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel173
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 173 j q :=
  degreePropagationTail 173 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel173

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel174
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 174 j q :=
  degreePropagationTail 174 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel174

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel175
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 175 j q :=
  degreePropagationTail 175 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel175

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel176
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 176 j q :=
  degreePropagationTail 176 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel176

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel177
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 177 j q :=
  degreePropagationTail 177 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel177

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel178
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 178 j q :=
  degreePropagationTail 178 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel178

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel179
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 179 j q :=
  degreePropagationTail 179 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel179

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel180
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 180 j q :=
  degreePropagationTail 180 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel180

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel181
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 181 j q :=
  degreePropagationTail 181 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel181

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel182
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 182 j q :=
  degreePropagationTail 182 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel182

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel183
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 183 j q :=
  degreePropagationTail 183 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel183

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel184
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 184 j q :=
  degreePropagationTail 184 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel184

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel185
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 185 j q :=
  degreePropagationTail 185 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel185

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel186
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 186 j q :=
  degreePropagationTail 186 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel186

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel187
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 187 j q :=
  degreePropagationTail 187 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel187

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel188
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 188 j q :=
  degreePropagationTail 188 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel188

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel189
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 189 j q :=
  degreePropagationTail 189 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel189

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel190
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 190 j q :=
  degreePropagationTail 190 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel190

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel191
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 191 j q :=
  degreePropagationTail 191 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel191

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel192
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 192 j q :=
  degreePropagationTail 192 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel192

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel193
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 193 j q :=
  degreePropagationTail 193 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel193

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel194
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 194 j q :=
  degreePropagationTail 194 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel194

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel195
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 195 j q :=
  degreePropagationTail 195 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel195

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel196
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 196 j q :=
  degreePropagationTail 196 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel196

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel197
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 197 j q :=
  degreePropagationTail 197 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel197

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel198
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 198 j q :=
  degreePropagationTail 198 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel198

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel199
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 199 j q :=
  degreePropagationTail 199 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel199

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel200
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 200 j q :=
  degreePropagationTail 200 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel200

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel201
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 201 j q :=
  degreePropagationTail 201 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel201

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel202
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 202 j q :=
  degreePropagationTail 202 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel202

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel203
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 203 j q :=
  degreePropagationTail 203 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel203

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel204
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 204 j q :=
  degreePropagationTail 204 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel204

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel205
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 205 j q :=
  degreePropagationTail 205 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel205

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel206
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 206 j q :=
  degreePropagationTail 206 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel206

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel207
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 207 j q :=
  degreePropagationTail 207 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel207

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel208
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 208 j q :=
  degreePropagationTail 208 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel208

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel209
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 209 j q :=
  degreePropagationTail 209 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel209

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel210
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 210 j q :=
  degreePropagationTail 210 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel210

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel211
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 211 j q :=
  degreePropagationTail 211 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel211

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel212
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 212 j q :=
  degreePropagationTail 212 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel212

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel213
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 213 j q :=
  degreePropagationTail 213 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel213

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel214
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 214 j q :=
  degreePropagationTail 214 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel214

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel215
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 215 j q :=
  degreePropagationTail 215 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel215

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel216
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 216 j q :=
  degreePropagationTail 216 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel216

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel217
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 217 j q :=
  degreePropagationTail 217 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel217

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel218
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 218 j q :=
  degreePropagationTail 218 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel218

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel219
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 219 j q :=
  degreePropagationTail 219 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel219

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel220
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 220 j q :=
  degreePropagationTail 220 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel220

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel221
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 221 j q :=
  degreePropagationTail 221 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel221

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel222
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 222 j q :=
  degreePropagationTail 222 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel222

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel223
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 223 j q :=
  degreePropagationTail 223 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel223

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel224
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 224 j q :=
  degreePropagationTail 224 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel224

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel225
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 225 j q :=
  degreePropagationTail 225 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel225

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel226
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 226 j q :=
  degreePropagationTail 226 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel226

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel227
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 227 j q :=
  degreePropagationTail 227 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel227

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel228
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 228 j q :=
  degreePropagationTail 228 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel228

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel229
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 229 j q :=
  degreePropagationTail 229 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel229

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel230
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 230 j q :=
  degreePropagationTail 230 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel230

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel231
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 231 j q :=
  degreePropagationTail 231 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel231

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel232
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 232 j q :=
  degreePropagationTail 232 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel232

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel233
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 233 j q :=
  degreePropagationTail 233 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel233

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel234
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 234 j q :=
  degreePropagationTail 234 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel234

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel235
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 235 j q :=
  degreePropagationTail 235 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel235

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel236
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 236 j q :=
  degreePropagationTail 236 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel236

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel237
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 237 j q :=
  degreePropagationTail 237 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel237

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel238
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 238 j q :=
  degreePropagationTail 238 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel238

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel239
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 239 j q :=
  degreePropagationTail 239 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel239

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel240
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 240 j q :=
  degreePropagationTail 240 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel240

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel241
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 241 j q :=
  degreePropagationTail 241 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel241

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel242
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 242 j q :=
  degreePropagationTail 242 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel242

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel243
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 243 j q :=
  degreePropagationTail 243 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel243

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel244
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 244 j q :=
  degreePropagationTail 244 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel244

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel245
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 245 j q :=
  degreePropagationTail 245 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel245

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel246
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 246 j q :=
  degreePropagationTail 246 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel246

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel247
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 247 j q :=
  degreePropagationTail 247 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel247

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel248
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 248 j q :=
  degreePropagationTail 248 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel248

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel249
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 249 j q :=
  degreePropagationTail 249 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel249

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel250
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  degreePropagationTail 250 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel251
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  degreePropagationTail 251 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel252
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  degreePropagationTail 252 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel253
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  degreePropagationTail 253 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel254
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  degreePropagationTail 254 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel255
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  degreePropagationTail 255 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel256
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  degreePropagationTail 256 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel257
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  degreePropagationTail 257 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel258
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  degreePropagationTail 258 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel259
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  degreePropagationTail 259 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel260
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  degreePropagationTail 260 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel261
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  degreePropagationTail 261 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel262
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  degreePropagationTail 262 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel263
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  degreePropagationTail 263 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel264
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  degreePropagationTail 264 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel265
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  degreePropagationTail 265 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel266
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  degreePropagationTail 266 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel267
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  degreePropagationTail 267 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel268
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  degreePropagationTail 268 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel269
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  degreePropagationTail 269 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel270
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  degreePropagationTail 270 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel271
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  degreePropagationTail 271 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel272
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  degreePropagationTail 272 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel273
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  degreePropagationTail 273 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel274
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  degreePropagationTail 274 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel275
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  degreePropagationTail 275 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel276
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  degreePropagationTail 276 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel277
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  degreePropagationTail 277 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel278
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  degreePropagationTail 278 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel279
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  degreePropagationTail 279 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel280
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  degreePropagationTail 280 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel281
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  degreePropagationTail 281 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel282
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  degreePropagationTail 282 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel283
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  degreePropagationTail 283 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel284
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  degreePropagationTail 284 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel285
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  degreePropagationTail 285 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel286
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  degreePropagationTail 286 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel287
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  degreePropagationTail 287 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel288
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  degreePropagationTail 288 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel289
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  degreePropagationTail 289 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel290
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  degreePropagationTail 290 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel291
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  degreePropagationTail 291 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel292
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  degreePropagationTail 292 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel293
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  degreePropagationTail 293 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel294
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  degreePropagationTail 294 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel295
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  degreePropagationTail 295 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel296
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  degreePropagationTail 296 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel297
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  degreePropagationTail 297 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel298
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  degreePropagationTail 298 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel299
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  degreePropagationTail 299 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel299

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel300
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 300 j q :=
  degreePropagationTail 300 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel300

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel301
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 301 j q :=
  degreePropagationTail 301 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel301

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel302
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 302 j q :=
  degreePropagationTail 302 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel302

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel303
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 303 j q :=
  degreePropagationTail 303 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel303

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel304
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 304 j q :=
  degreePropagationTail 304 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel304

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel305
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 305 j q :=
  degreePropagationTail 305 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel305

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel306
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 306 j q :=
  degreePropagationTail 306 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel306

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel307
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 307 j q :=
  degreePropagationTail 307 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel307

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel308
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 308 j q :=
  degreePropagationTail 308 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel308

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel309
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 309 j q :=
  degreePropagationTail 309 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel309

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel310
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 310 j q :=
  degreePropagationTail 310 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel310

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel311
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 311 j q :=
  degreePropagationTail 311 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel311

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel312
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 312 j q :=
  degreePropagationTail 312 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel312

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel313
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 313 j q :=
  degreePropagationTail 313 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel313

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel314
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 314 j q :=
  degreePropagationTail 314 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel314

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel315
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 315 j q :=
  degreePropagationTail 315 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel315

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel316
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 316 j q :=
  degreePropagationTail 316 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel316

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel317
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 317 j q :=
  degreePropagationTail 317 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel317

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel318
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 318 j q :=
  degreePropagationTail 318 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel318

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel319
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 319 j q :=
  degreePropagationTail 319 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel319

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel320
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 320 j q :=
  degreePropagationTail 320 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel320

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel321
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 321 j q :=
  degreePropagationTail 321 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel321

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel322
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 322 j q :=
  degreePropagationTail 322 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel322

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel323
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 323 j q :=
  degreePropagationTail 323 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel323

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel324
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 324 j q :=
  degreePropagationTail 324 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel324

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel325
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 325 j q :=
  degreePropagationTail 325 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel325

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel326
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 326 j q :=
  degreePropagationTail 326 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel326

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel327
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 327 j q :=
  degreePropagationTail 327 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel327

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel328
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 328 j q :=
  degreePropagationTail 328 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel328

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel329
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 329 j q :=
  degreePropagationTail 329 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel329

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel330
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 330 j q :=
  degreePropagationTail 330 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel330

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel331
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 331 j q :=
  degreePropagationTail 331 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel331

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel332
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 332 j q :=
  degreePropagationTail 332 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel332

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel333
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 333 j q :=
  degreePropagationTail 333 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel333

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel334
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 334 j q :=
  degreePropagationTail 334 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel334

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel335
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 335 j q :=
  degreePropagationTail 335 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel335

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel336
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 336 j q :=
  degreePropagationTail 336 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel336

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel337
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 337 j q :=
  degreePropagationTail 337 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel337

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel338
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 338 j q :=
  degreePropagationTail 338 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel338

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel339
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 339 j q :=
  degreePropagationTail 339 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel339

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel340
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 340 j q :=
  degreePropagationTail 340 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel340

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel341
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 341 j q :=
  degreePropagationTail 341 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel341

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel342
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 342 j q :=
  degreePropagationTail 342 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel342

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel343
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 343 j q :=
  degreePropagationTail 343 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel343

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel344
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 344 j q :=
  degreePropagationTail 344 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel344

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel345
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 345 j q :=
  degreePropagationTail 345 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel345

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel346
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 346 j q :=
  degreePropagationTail 346 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel346

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel347
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 347 j q :=
  degreePropagationTail 347 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel347

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel348
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 348 j q :=
  degreePropagationTail 348 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel348

namespace ForestUnimodality.Stage170KernelData.Cell320.Kernel349
open FiniteKernelRationalCertificate
theorem checked : row.degreePropagationCheck 131 interval.lo interval.hi = true :=
  degreePropagationThreshold

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 349 j q :=
  degreePropagationTail 349 (by decide +kernel) j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell320.Kernel349

